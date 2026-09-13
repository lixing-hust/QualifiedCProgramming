# QCP+LLM 框架下操作系统内核函数自动验证的可行性实验报告

## 摘要

本报告评估将 QCP（Qualified C Programming）与大语言模型结合，用于操作系统内核 C 函数自动验证的可行性。实验选取 CertiUCOS capability 子系统中的两个函数：底层能力更新函数 `ucos_Grant_Cap`，以及调用它的用户接口函数 `grant_cspace_cap`。原函数来自 `QCP_examples/osverify/certiucos/code/ios_cap.v` 中的 C 风格深嵌入语言实现，本实验将其迁移为 QCP 可处理的 C 程序，并复用原项目规格所表达的主要行为。

两次实验均完成了从 C annotation、符号执行、VC 生成、LLM 辅助证明、Coq 检查到最终新鲜度检查的完整流程，controller 最终状态均为 `done`。其中：

- `ucos_Grant_Cap` 生成的 21 个证明义务均由自动证明层处理，最终没有 manual VC；
- 包含 caller/callee 的 `grant_cspace_cap` 组合 case 共生成 81 个 goal definitions，其中 auto 文件包含 61 个证明 lemma；controller 另识别出 10 个 top-level manual VC，并产生 4 个 split goal，由 LLM 分组完成 Coq 证明；
- 最终 manual 和可编辑 case lib 中没有 `Admitted.` 或额外 `Axiom`，也没有未封闭的目标；独立 symbolic execution freshness 和完整 `goal_check` 均通过。

实验结果表明：对于顺序执行的内核叶子函数和一层调用包装函数，QCP+LLM 已具备端到端验证的工程可行性。但这仍是概念验证，尚不能推出整个内核可自动验证；尤其是中断、抢占、临界区并发语义，以及原 osverify 全局 `OSInv` 的完整迁移，仍需后续工作。

## 1. 研究问题与结论

本实验要回答的问题是：

> 在不预先手写全部 Coq 证明的情况下，能否由 LLM 完成内核函数的规格适配、VC 分析和证明构造，同时由 QCP 与 Coq 提供确定性的可信检查？

当前结论是“有限范围内可行”：

1. 对局部 capability 更新函数，可实现高度自动化验证；
2. 对包含全局状态访问、权限判断和已验证函数调用的 wrapper，也能完成组合验证；
3. LLM 输出不直接作为可信结论，最终可信性来自 QCP 符号执行、controller 的版本与结构门禁，以及 Coq 内核检查；
4. 当前结论只覆盖顺序语义和实验中给出的规格，不覆盖真实并发执行，也没有形式化证明迁移后的 C 与原深嵌入语言程序完全等价。

因此，更准确的表述是：该框架实现了“LLM 辅助生成、QCP/Coq 机械验收”的半自动内核函数验证，而不是无需规格设计和程序准备的全自动内核验证。

## 2. 实验对象

### 2.1 `ucos_Grant_Cap`

该函数是 capability 子系统的底层内核函数，主要行为为：

1. 检查 capability class 是否位于合法范围 `0..CAP_CHANNEL_CLASS`；
2. 检查目标任务优先级是否能索引 `OSCSpacePrioTbl`；
3. 检查目标任务的 CSpace 是否存在；
4. 成功时更新目标 slot 的 capability type、category content 和 rights；
5. 新 rights 为 `(old_right & 4095) | requested_right`；
6. 非法输入或空 CSpace 返回 `CNODE_GRANT_FAILURE`，成功返回 `CNODE_NONE_FAULT`。

QCP C 实现及规格位于：

- `QCP_examples/osverify_qcp/cases/ucos_Grant_Cap.c`
- 原实现：`QCP_examples/osverify/certiucos/code/ios_cap.v`
- 原规格：`QCP_examples/osverify/certiucos/proofs/capability/lib/CapSpec.v`

### 2.2 `grant_cspace_cap`

该函数是上层用户接口，除参数检查外，还会：

1. 从 `OSTCBCur` 读取当前任务优先级并更新 `OSPrioCur`；
2. 从 `OSCSpacePrioTbl` 取得当前任务 CSpace；
3. 检查当前 CSpace 的 `CNODE_GRANT_CAP` 权限位；
4. 检查 `CapParent[dest]` 是否等于当前任务；
5. 权限允许时调用 `ucos_Grant_Cap`；
6. 根据失败位置返回 `OS_PRIO_INVALID`、`CNODE_GRANT_FAILURE`、`USER_CAPABILITY_NONE` 或 `CSPACE_NONE_FAULT`。

原程序在上述共享状态操作前后执行 `ENTER_CRITICAL/EXIT_CRITICAL`。本实验首先验证顺序功能，因此在迁移后的 C 中将它们保留为注释形式的 no-op 边界，不对关中断、互斥或其他线程无干扰作任何证明。

对应文件为：

- 顺序版 C 与 annotation：`QCP_examples/osverify_qcp/cases/ucos_Grant_Cap.c`
- 原实现：`QCP_examples/osverify/certiucos/code/ios_cap.v`
- 原抽象操作规格：`QCP_examples/osverify/certiucos/spec/abs_op_capability.v`

## 3. QCP+LLM 验证流程

本实验的实际流程为：

```text
原 osverify 实现/规格
        ↓
顺序 C 转写与 QCP separation-logic annotation
        ↓
QCP symbolic execution
        ↓
自动 VC + manual VC
        ↓
LLM 分析、分组、生成 Coq proof
        ↓
每组 exact Coq check
        ↓
controller 机械合并与 parent full check
        ↓
独立 symexec freshness + final goal_check
        ↓
done
```

框架中的职责边界如下：

| 层次 | 主要职责 | 是否属于最终信任依据 |
|---|---|---|
| LLM annotation agent | 设计/修正规格、资源 footprint、调用实例 | 否，候选必须重新检查 |
| QCP symbolic execution | 根据 C 与 annotation 生成验证条件 | 是，依赖 QCP 语义与实现正确性 |
| LLM VC-checking/group workers | 选择证明模式、分组并构造 Coq proof | 否，proof 必须被 Coq 接受 |
| Controller | 封存版本、检查 witness 覆盖、隔离 proof group、机械合并、拒绝 stale artifact | 是，作为实验验收流程的一部分 |
| Coq kernel | 检查所有最终证明项 | 是，最终逻辑可信核心 |

这种结构降低了 LLM 幻觉直接进入结论的风险：LLM 可以提出错误 annotation 或 proof，但无法让没有通过 symbolic execution、Coq 和 final-check 的结果被标记为完成。

## 4. Case 1：`ucos_Grant_Cap`

### 4.1 规格设计

规格使用 separation logic 精确描述：

- `OSCSpacePrioTbl[dest]` 表项；
- 目标 CSpace 是否为空；
- 目标 capability 的 `cap_type`、`category_content` 和 `category_right`；
- 成功路径上的字段更新；
- 失败路径上的内存保持不变。

该规格不仅检查返回值，还检查 capability 内存状态是否发生了正确变换。

### 4.2 验证结果

独立 run：`ucos_Grant_Cap-20260910000144`。

- 最终 controller phase：`done`；
- goal definitions：21；
- auto proof lemmas：21；
- manual target witnesses：0；
- proof groups：0；
- 总墙钟时间：3103.37 秒，约 51 分 43 秒；
- finalization：43.89 秒。

“manual target witnesses 为 0”表示最终 annotation 形成后，所有 VC 均已被 QCP 自动证明层处理。总耗时主要来自前期规格设计和修正，而不是 Coq 最终编译。

该 standalone run 在当时封存的 C/annotation 版本上完成。为了支持后续 caller 组合，当前工作树中的 callee 契约后来被拆分为四个具名规格，因此旧 run 的 generated 文件不再代表当前 C 文件的新鲜输出；旧版本仍保存在该 run 的 annotation history 中。修改后的 callee 已在下面的 `grant_cspace_cap` 组合 run 中重新生成并验证。

## 5. Case 2：`grant_cspace_cap` 调用 `ucos_Grant_Cap`

### 5.1 首次失败暴露的问题

第一次 annotation attempt 中，controller 调用 symbolic execution 返回成功，但目标 C 文件实际只包含 `ucos_Grant_Cap`，没有 `grant_cspace_cap`。因此生成文件只有 callee obligations，没有任何 wrapper witness。

该问题没有被误判成验证成功：annotation agent 将其报告为 `missing-target-function`，controller 拒绝进入证明阶段。随后补充顺序版 wrapper，再使用同一持续 annotation 会话重新生成规格和 VC。

这一过程说明，仅以“symexec 进程退出码为 0”判断成功是不够的；必须同时检查目标函数 witness 是否存在、是否完整覆盖、生成结果是否与封存源码对应。

### 5.2 Caller/callee 契约组合

原先 `ucos_Grant_Cap` 使用一个包含多个析取分支的大规格。对单函数验证而言可以使用，但 wrapper 在具体控制流分支上调用时，容易引入无关分支和互相不一致的资源变量。

最终将 callee 拆分为四个语义等价的具名规格：

- `class_invalid`：capability class 非法；
- `prio_invalid`：目标优先级不能安全索引表；
- `null_target`：目标 CSpace 为空；
- `valid_target`：目标存在并执行 capability 更新。

wrapper 调用点再根据当前路径条件，通过 branch-scoped `where` 选择：

- `callee_invalid`；
- `callee_null`；
- `callee_success`。

这样既重新验证了修改后的 callee，也使 caller 的 call VC 只携带当前分支实际需要的资源和纯条件。旧的独立 `ucos_Grant_Cap_*` generated artifact 没有被直接作为可信依赖；修改后的 callee obligations 被重新生成在 `grant_cspace_cap_*` 组合 case 中，并随 caller 一起通过最终检查。

### 5.3 共享状态 footprint

wrapper 规格显式覆盖：

- 当前 TCB 与 `OSTCBPrio`；
- 全局 `OSPrioCur`；
- `OSRunning`；
- 当前任务和目标任务的 `OSCSpacePrioTbl` 表项；
- 当前 CSpace 的 grant-right slot；
- `CapParent[dest]`；
- callee 需要的目标 capability 字段。

成功路径反映目标 capability 的精确更新；失败路径保持相应共享资源不变。该 footprint 比只描述三个局部参数更适合 caller/callee 组合，但仍不是原 osverify 完整 `OSInv` 的等价迁移。

### 5.4 验证结果

组合 run：`grant_cspace_cap-20260913165358`。

- 最终 controller phase：`done`；
- goal definitions：81，包含重新生成的 callee 和 caller obligations；
- auto proof lemmas：61；
- manual top-level witnesses：10；
- split goals：4；
- 最终 manual proof lemmas：14；
- proof groups：4；
- 总墙钟时间：3608.47 秒，约 60 分 08 秒；
- parent full check：32.88 秒；
- finalization：40.00 秒。

10 个 manual top-level VC 中，4 个采用 `aggressive_pre_process` 的 split-first 路线，6 个采用 `LLM_pre_process` 的整体证明路线。分组如下：

| Proof group | Top-level VC 数 | 主要内容 |
|---|---:|---|
| `cap-update-success` | 2 | callee 更新 capability，以及 wrapper 成功状态投影 |
| `active-return-projections` | 3 | 授权路径上的返回状态与纯条件 |
| `grant-bit-clear-returns` | 3 | grant 权限位未设置时的失败分支 |
| `callee-error-returns` | 2 | callee 的非法 class 和空目标失败分支 |

4 个 group 均通过独立 exact group check；controller 机械合并后，parent full Coq check 和最终正式路径检查均通过。

## 6. 定量对比

| 指标 | `ucos_Grant_Cap` | `grant_cspace_cap` 组合 case |
|---|---:|---:|
| 函数层次 | 叶子函数 | wrapper + callee |
| Annotation attempts | 3 | 2 |
| Goal definitions | 21 | 81 |
| Auto proof lemmas | 21 | 61 |
| Manual top-level VC | 0 | 10 |
| Manual split goals | 0 | 4 |
| Proof groups | 0 | 4 |
| Parent full check | 0.24 秒 | 32.88 秒 |
| 总墙钟时间 | 51 分 43 秒 | 60 分 08 秒 |
| 最终状态 | `done` | `done` |

墙钟时间包含 LLM 分析、等待、annotation 重试和 controller 检查，不能解释为纯求解器 CPU 时间。两次实验的共同特征是：耗时主要集中在规格和资源 footprint 的形成，而非最终 Coq proof checking。

## 7. 对可行性的判断

### 7.1 已得到实验支持的能力

1. **内存安全验证**：数组索引、指针解引用和结构体字段访问都产生并完成相应安全义务。
2. **功能正确性验证**：返回码及 capability rights 更新与规格一致。
3. **函数调用组合**：wrapper 可以调用同一 case 内重新验证的 callee，而非把调用结果当作无条件公理。
4. **共享状态 framing**：与调用无关的 TCB、授权位和表项资源能够在调用前后保持。
5. **自动/LLM 混合求解**：简单义务由自动层完成，剩余 VC 可由 LLM 分组并生成可被 Coq 接受的证明。
6. **结果防漂移**：controller 绑定源码、generated goal、witness statement 和证明版本，并在最终阶段重新运行 symbolic execution。

### 7.2 当前可行性等级

| 场景 | 当前判断 | 依据 |
|---|---|---|
| 小型顺序叶子函数 | 高 | `ucos_Grant_Cap` 无 manual VC 完成 |
| 一层 wrapper/callee 组合 | 中高 | `grant_cspace_cap` 的 10 个 manual VC 完成 |
| 多函数共享全局状态 | 中 | footprint 方法可工作，但规格规模可能快速增长 |
| 原 `OSInv` 的整体迁移 | 尚待验证 | 当前只建模与两个函数直接相关的共享资源 |
| 中断/临界区并发正确性 | 未验证 | `ENTER/EXIT_CRITICAL` 当前按顺序 no-op 处理 |
| 整个操作系统内核自动验证 | 证据不足 | 目前只有两个同一子系统的小型函数 |

## 8. 局限与可信边界

### 8.1 并发未纳入本次结论

原函数使用 `ENTER_CRITICAL/EXIT_CRITICAL` 防止中断或并发干扰。本实验没有证明：

- 关中断指令的机器语义；
- 临界区期间其他线程或中断不能修改共享状态；
- 临界区嵌套、恢复和抢占行为正确。

QCP 底层存在 `CriticalSTS` 和 `NestedCriticalSTS` 等逻辑组件，但当前 case 使用顺序规则，尚未把这些 STS 与 C 前端及临界区原语接通。

### 8.2 程序迁移的等价性尚未形式化

原程序是 osverify 的 C 风格深嵌入语言，本实验将其人工转写成 QCP C。当前通过了行为规格验证，但没有额外建立“原 DSL 程序与迁移后 C 程序语义等价”的形式化定理。因此，转写正确性仍属于人工审查边界。

### 8.3 规格正确性仍需专家确认

Coq 证明说明“程序满足所给规格”，不自动说明“规格完全表达了内核设计意图”。当前规格参考了原 `CapSpec.v` 和 `grant_cspace_cap_spec`，但尚未将原项目中的 `OSInv`、`CapabilityInv`、任务列表等整体不变量完全迁移。

### 8.4 样本规模有限

两个函数位于同一 capability 子系统，且不包含循环、递归、动态分配和复杂调度。因此目前只能说明方法具备扩展基础，不能据此估计整个 CertiUCOS 的平均验证成本。

### 8.5 信任基础

最终结论依赖：

- Coq 内核；
- QCP separation logic 与 symbolic execution 的正确性；
- C 数据布局和整数模型与目标平台的一致性；
- 用户提供/LLM 构造规格对设计意图的忠实性；
- controller 的版本封存和验收实现。

LLM 本身不属于逻辑信任核心，因为所有 LLM 生成的 proof 都必须经过 Coq 检查。

## 9. 后续研究建议

1. **建立可复用内核状态谓词**：把 CSpace 表、TCB、`CapParent` 和 capability slots 抽象成 reusable separation-logic predicates，避免每个函数重复展开局部 footprint。
2. **建立原规格桥接定理**：证明 QCP 函数规格蕴含或等价于原 `ucos_Grant_Cap_spec`、`grant_cspace_cap_spec`，把“参考原规格”提升为机械证明。
3. **扩展到同模块更多函数**：优先验证 `user_cnode_mint`、`user_cnode_copy`、`Get_Obj_Slot` 等，以观察调用深度、循环和资源别名对成本的影响。
4. **接入临界区抽象**：先把 `ENTER/EXIT_CRITICAL` 建模为可信原语和资源所有权转移，再接入 `CriticalSTS`/`NestedCriticalSTS`；最后才考虑机器级中断语义。
5. **扩大实验样本**：建议至少覆盖 10–20 个函数，并记录 annotation attempts、VC 数、自动证明比例、人工源代码修改量和总时间。
6. **做重复性实验**：对同一批函数进行多次独立 LLM run，比较成功率、proof 稳定性和成本波动。

可将下一阶段的验收目标设为：同一子系统至少 10 个函数全部通过 fresh symexec 和 final `goal_check`；不存在 `Admitted.`/额外 `Axiom`；callee 契约可被至少两个 caller 复用；至少一个循环函数完成验证；并为每个 QCP 规格提供到原 osverify 抽象规格的桥接说明或定理。

## 10. 实验证据与复现入口

### `ucos_Grant_Cap`

- C 与 annotation：`QCP_examples/osverify_qcp/cases/ucos_Grant_Cap.c`
- Generated goal：`Rocq/examples/osverify_qcp/cases/ucos_Grant_Cap_goal.v`
- Auto proof：`Rocq/examples/osverify_qcp/cases/ucos_Grant_Cap_proof_auto.v`
- Goal check：`Rocq/examples/osverify_qcp/cases/ucos_Grant_Cap_goal_check.v`
- Controller state：`reports/ucos_Grant_Cap-20260910000144/controller_state.json`
- Timing：`reports/ucos_Grant_Cap-20260910000144/timing_summary.json`

### `grant_cspace_cap`

- C、caller/callee 规格与调用实例：`QCP_examples/osverify_qcp/cases/ucos_Grant_Cap.c`
- Generated goal：`Rocq/examples/osverify_qcp/cases/grant_cspace_cap_goal.v`
- Auto proof：`Rocq/examples/osverify_qcp/cases/grant_cspace_cap_proof_auto.v`
- Manual proof：`Rocq/examples/osverify_qcp/cases/grant_cspace_cap_proof_manual.v`
- Goal check：`Rocq/examples/osverify_qcp/cases/grant_cspace_cap_goal_check.v`
- Controller state：`reports/grant_cspace_cap-20260913165358/controller_state.json`
- Group plan：`reports/grant_cspace_cap-20260913165358/rounds/grant_cspace_cap-vc-checking-r1/group_plan.json`
- Timing：`reports/grant_cspace_cap-20260913165358/timing_summary.json`

## 11. 总结

这两个 case 给出了一个清晰的概念验证：QCP+LLM 能够把操作系统内核中的顺序 C 函数从“程序和非形式化/旧框架规格”推进到“由 Coq 检查的完整证明”。叶子函数可以达到接近全自动的结果；当出现共享全局状态和函数调用时，LLM 能辅助完成规格拆分、调用实例化、VC 分组和证明生成，而 controller 能阻止目标缺失、版本漂移或未完成证明被误报为成功。

目前最主要的瓶颈不是 Coq 对最终 proof 的检查速度，而是可扩展、可复用且忠实于原内核抽象的规格工程。下一阶段若能完成共享 `OSInv` 谓词、原规格桥接以及临界区 STS 接入，便可以更有力地评估该方法从函数级概念验证扩展到内核子系统级验证的可行性。
