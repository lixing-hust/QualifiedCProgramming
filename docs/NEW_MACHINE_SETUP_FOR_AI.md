# 给大模型的新电脑配置任务：QCP + osverify

请在这台电脑上实际完成下述安装、构建和验收，不要只给建议。目标是从 GitHub 下载项目后，运行 QCP、复查已有例子的证明，并构建 osverify。保留已有证明，不重新设计规格或重新证明题目。

## 1. 先明确环境和边界

- 仓库：`https://github.com/lixing-hust/QualifiedCProgramming.git`。
- 本说明编写于 2026-10-14，对照提交：`a58351f3fc2b5f24b0980553fb6167c180e777fb`，当时与 origin HEAD 相同。实际操作必须记录当前 commit，不能假设后续版本路径不变。
- 默认方案：Windows x86_64 上使用 WSL2 Ubuntu 22.04；原生 Ubuntu x86_64 跳过 WSL 安装。在 ARM 或其他系统上，先确认二进制架构，不运行不匹配的 `linux-binary`。
- 普通系统包安装、创建独立 opam switch、项目虚拟环境、构建及可恢复的配置修正属于本任务。需要管理员密码或 Windows 重启时，准确告诉用户操作步骤；其余步骤持续执行。
- 不推送 Git，不覆盖用户文件，不删除旧环境，不改业务代码、数学规格、证明和 generated `.v` 来掩盖配置错误。不加入 `Admitted` 或 `Axiom`。
- 不安装 Lean、MCP 或编辑器插件作为命令行验收的前置条件。VS Code/QIDE 可最后选装。编译已有证明不需要大模型 API 密钥；自动生成新证明的 agent 运行环境是另一项配置。
- 读取当前 `AGENTS.md`、README、适用的 setup 文档和实际 controller 路径。本文用于机器初始化，不取代正式验证流程的写入边界。

## 2. Windows 上先准备 WSL

已有可用 Ubuntu WSL2 则复用，不重复安装。Windows PowerShell 中先查看：

```powershell
wsl --list --verbose
```

未安装时，在管理员 PowerShell 执行：

```powershell
wsl --install -d Ubuntu-22.04
```

按提示重启，启动 Ubuntu，创建 Linux 用户。此后所有 Linux 命令都在 Ubuntu 中执行。不要混用 Windows 的 Python、opam、Coq 或 Git。

若要完整重编 osverify，优先使用 32 GB 内存电脑。可在这种机器的 `%USERPROFILE%\.wslconfig` 中合并以下配置；保留已有其他设置，不能盲目覆盖文件：

```ini
[wsl2]
memory=16GB
swap=16GB
```

保存工作后在 Windows 执行 `wsl --shutdown`，再打开 Ubuntu。该命令会停止其他 WSL 工作；不要在构建途中执行。内存较小的机器需按实际资源调整，并记录约束，不能承诺同样完成时间。

## 3. 下载代码与系统依赖

在 Linux 中安装依赖：

```bash
sudo apt update
sudo apt install -y git curl ca-certificates build-essential opam bubblewrap libgmp-dev pkg-config unzip m4 time file
mkdir -p ~/projects
cd ~/projects
git clone --recurse-submodules https://github.com/lixing-hust/QualifiedCProgramming.git
cd QualifiedCProgramming
git submodule update --init --recursive
git rev-parse HEAD
git status --short
```

已有 checkout 时先检查 origin 和改动，不能重复 clone 或直接 reset。项目应放在 Linux 的 `~/projects`，不要在 `/mnt/c/.../Desktop` 上做大量 Coq 编译。

GitHub 不包含 `.venv`、opam 环境、`CONFIGURE`、`.vo/.glob`、`reports/` 和 `verification_runs/` 等本地内容。必须重建环境和产物，不能要求用户从旧电脑复制这些目录，也不能把缺少旧报告当成源码缺失。

osverify 源码、`_CoqProject`、兼容层 `Lia.v`、`Omega.v` 在上述提交中已纳入 Git。其 `CoqMakefile` 是本机生成文件，需要重新生成。

## 4. 安装两套隔离的 Coq

| 用途 | switch 名 | OCaml | Coq |
| --- | --- | --- | --- |
| 当前 QCP / Rocq | qcp-rocq | 4.14.1 | 8.20.1 |
| osverify 已适配版本 | osverify-coq815 | 4.14.0 | 8.15.2 |

QCP 的版本来自当前 README/dune-project；osverify 的版本来自原机器已完成构建的独立 switch。不要给两个项目统一升级 Coq，也不要为当前适配后的 osverify 安装最早的 Coq 8.4pl6。

先查看 `opam switch list`。仅在尚未初始化时执行 `opam init -y`；仅在对应 switch 不存在时执行 create。已有同名 switch 要检查实际版本，不直接重装。

```bash
opam init -y
opam update
opam switch create qcp-rocq ocaml-base-compiler.4.14.1 -y
opam install --switch=qcp-rocq coq.8.20.1 'dune>=3.16.1' -y
opam switch create osverify-coq815 ocaml-base-compiler.4.14.0 -y
opam install --switch=osverify-coq815 coq.8.15.2 -y
```

构建命令始终显式使用 `opam exec --switch=... -- ...`。版本检查可使用该入口执行 `coqc --version` 和 `ocamlc -version`；这里只查询工具版本，不直接运行 case 的 raw Coq 检查。

安装 Dune 是满足当前工具链要求，不意味着可以绕过仓库的 controller/build 规则自行选择 Dune 验证 case。

## 5. Python 与 controller

安装 uv；若已经可用则跳过安装：

```bash
curl -LsSf https://astral.sh/uv/install.sh -o /tmp/qcp-install-uv.sh
sh /tmp/qcp-install-uv.sh
export PATH="$HOME/.local/bin:$PATH"
```

在仓库根目录执行：

```bash
uv python install 3.12
uv sync --frozen --managed-python --python 3.12
.venv/bin/python --version
```

必须为 uv 管理的 Python 3.12，不能用系统 Python 替代；不能修改 `uv.lock` 来解决安装问题。若旧 `.venv` 指向其他机器，先备份并重建。若 uv cache 权限错误，可设置 `UV_CACHE_DIR=/tmp/qcp-uv-cache` 后重试。

上述提交的 controller 实际位于：

```text
.agents/scripts/verification-orchestrator/controller.py
```

执行其 `--help` 检查 Python 环境和入口。旧说明中出现的 `.agents/skills/verification-orchestrator/scripts/controller.py` 在该提交中不存在。当前路径合同为 `.agents/skills/verification-orchestrator/workflows/paths-and-commands.md`。若当前 commit 又发生迁移，先定位公共入口；不要执行内部模块。

## 6. QCP 基础库构建

当前正式库在 `Rocq/`。根目录残留的 `SeparationLogic/` 不代表仍有完整旧版源码，不要凭旧对话路径构建。

先检查 `linux-binary/symexec` 的架构、执行权限和动态库依赖；缺权限时只修复需要执行的文件。缺依赖时按真实 diagnostic 安装，不猜一组旧系统库。

当前仓库同时有 Makefile 和 Dune 支持，但历史 AGENTS/文档存在不同工作流。默认采用 Makefile 初始化，以满足本任务携带的 controller 规则；不要因 README 推荐 Dune 就忽略更具体的 AGENTS 约束。

检查 `Rocq/CONFIGURE`、`Rocq/unifysl/CONFIGURE`。如果没有，由本机生成；如果有，备份后修正旧机器绝对路径。`COQBIN` 必须对应 `opam var bin --switch=qcp-rocq` 的结果并带末尾 `/`，`SUF` 为空。不要写死 `/home/lixing/...`。

在仓库根，当前 Makefile 的初始化命令为：

```bash
opam exec --switch=qcp-rocq -- make -C Rocq/unifysl depend
opam exec --switch=qcp-rocq -- make -C Rocq/unifysl -j1
opam exec --switch=qcp-rocq -- make -C Rocq depend
opam exec --switch=qcp-rocq -- make -C Rocq -j1
```

先确认目标和配置与 checkout 一致，再执行。此处是机器首次基础构建；之后 case 的 symexec、coq-check、coq-debug 都必须走当前公共 controller 和它生成的命令，不自己拼 `-R`、include 或 overlay。

若全量目标中某个未完成示例失败，区分基础库失败和示例证明失败，记录实际目标。不能用“已安装 Coq”或“core 通过”冒充全量成功，也不能擅自填充证明来让环境验收变绿。

## 7. 已验证例子的复现：必须单独验收

基础库构建通过不等于用户以前验证的每个例子都通过。先查找已提交的 C、goal、auto、manual、goal_check、case lib 和原始 spec/coins，并列出可复查目标。

特别注意：该提交中旧 HumanEval 例子可能仍在 `QCP_examples/humaneval/`，不是当前 `Rocq/examples/` 默认构建覆盖的路径。例如：

```text
QCP_examples/humaneval/multi_dimensional_arrays/C_125.c
QCP_examples/humaneval/multi_dimensional_arrays/C_125_goal_check.v
QCP_examples/humaneval/multi_dimensional_arrays/C_125_proof_manual.v
QCP_examples/humaneval/multi_dimensional_arrays/coins_125.v
QCP_examples/humaneval/spec/125.v
```

先检查当前 controller/该目录说明是否支持这些现有文件的只读复查；不要直接创建一个同名新 run 重新生成并覆盖人工证明。若旧例子依赖旧版库或逻辑路径，明确列为兼容性问题；仅安装另一个 Coq switch 并不能补回缺失的旧版库。需要旧 commit 时使用独立 checkout，并先确认该版本，不改当前主目录来凑路径。

用户已经指定例子则逐个复查；尚未指定时，自主选择一个当前受支持、已有完整证明的例子做冒烟验收，并列出旧 HumanEval 的可用性与待处理项，不宣称“全部以前的例子可运行”。

QCP 验收分开记录：工具可以启动、基础库可构建、指定例子的 symbolic execution 成功、现有 manual 与 fixed goal check 通过。正式验证遵循当前技能和 controller 合同，不允许 raw symexec/raw coqc、手改 generated 文件或弱化规格。

不要执行 `run-example-linux.sh` 作为无害测试：它批量重新生成证明文件。若现有接口不能安全复查已证明例子，报告具体接口/版本缺口，不覆盖文件、不伪造通过结果。

## 8. 构建 osverify

这是独立 Coq 工程的构建，不是 QCP controller 的一个 C case。它使用自己的 `_CoqProject` 和 CoqMakefile；本节 coq_makefile/make 不用于绕过 QCP case 检查。

进入目录并重新生成本机 Makefile：

```bash
cd ~/projects/QualifiedCProgramming/QCP_examples/osverify
opam exec --switch=osverify-coq815 -- coq_makefile -f _CoqProject -o CoqMakefile
```

先验证 `_CoqProject` 列出的文件均存在。不要删除失败或缺失条目来得到成功。如果发现源码与上述已适配版本不同，报告 commit 差异。

原机器成功构建时使用 256 MiB 栈限制、16 GiB 虚拟地址上限及下面的 GC 参数。新机器先检查 `ulimit -Ss`、`ulimit -Hs`、`ulimit -Sv` 和 `free -h`；栈 hard limit 允许时将当前 shell soft stack 设置为：

```bash
ulimit -S -s 262144
```

不要误把“16 GiB 虚拟地址”当作必需 RSS；也不要施加 6/12 GiB 的低地址空间限制。原机器单个大证明曾达到约 8.75 GiB RSS，这是历史参考，不是新机器保证值。

从 osverify 目录执行，并保留完整日志和真实退出码：

```bash
OCAMLRUNPARAM='s=32M,o=20' opam exec --switch=osverify-coq815 -- make -f CoqMakefile -j1 > /tmp/qcp-osverify-build.log 2>&1
osverify_build_rc=$?
printf 'osverify build exit code: %s\n' "$osverify_build_rc"
```

必须等待实际进程退出。不能把启动成功、暂时无输出或已有部分 `.vo` 当成全量成功。失败时读取首个 diagnostic，区分版本、缺依赖、OOM 和证明问题。不要因一次 OOM 删改证明。

实际 build 退出码为 0 后检查：

```bash
opam exec --switch=osverify-coq815 -- make -f CoqMakefile -n
```

确认没有待编译目标，且没有残留构建进程。保留本次 `.vo` 供后续增量构建，不在成功后 make clean。

这里的“运行 osverify”是编译 Coq 证明工程，不是启动一个可运行的操作系统。`_CoqProject` 默认目标构建成功，也不自动等于最终 OS 定理及全部子项目、全部 assumptions 都通过审计。

## 9. 最终交付

在本机写 `LOCAL_SETUP_RESULT.md`，记录实际 commit、系统/架构、资源、两个 switch 的实际版本、Python 来源、配置路径、构建日志、退出码和未通过目标。这里只生成 Markdown，不复制旧机器的成功报告。

最终用中文告诉用户：

1. QCP 环境是否就绪，实际复查了哪些例子，哪些旧例子存在版本/路径问题。
2. osverify 是否真实全量完成，默认构建覆盖范围及剩余限制。
3. 两套环境各自可直接复制使用的命令，命令使用这台电脑真实路径。
4. 新终端需要的 opam/uv 设置、可选编辑器配置，以及必须由用户完成的重启或权限操作。

不要把尚未运行的验收标记通过。任务遇到可恢复安装/构建问题时继续修复；若只能靠改规格、补证明或找回未上传源码才能继续，明确给出证据和阻塞点。

## 官方参考

- WSL 安装与命令：https://learn.microsoft.com/en-us/windows/wsl/basic-commands
- WSL 资源配置：https://learn.microsoft.com/en-us/windows/wsl/wsl-config
- Coq 8.15.2 opam 包：https://opam.ocaml.org/packages/coq/coq.8.15.2/
- uv Python 管理：https://docs.astral.sh/uv/concepts/python-versions/
- uv 项目同步：https://docs.astral.sh/uv/concepts/projects/sync/
