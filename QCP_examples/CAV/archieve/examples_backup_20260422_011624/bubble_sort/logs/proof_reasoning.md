# Proof Reasoning

## Manual obligations

The strengthened annotations leave five manual witnesses:

- `bubble_sort_entail_wit_1`: initialize the outer invariant from the function precondition.
- `bubble_sort_entail_wit_2`: initialize the inner invariant from the outer invariant at the start of one pass.
- `bubble_sort_entail_wit_3_1`: preserve the inner invariant across the swap branch.
- `bubble_sort_entail_wit_4`: lift the inner invariant at loop exit to the next outer-loop state.
- `bubble_sort_return_wit_1`: derive the postcondition from the outer invariant at function exit.

## Intended proof structure

- `entail_wit_1`: choose `l_outer = l`, use reflexive permutation, note that `sublist(n, n, l)` is empty so `sorted_z` is immediate, and the cross-boundary ordering fact is vacuous.
- `entail_wit_2`: choose `l_inner = l_outer`, keep the same array contents, and show the prefix-maximum fact for `j = 0` by reflexivity.
- `entail_wit_3_1`: choose the swapped list produced by the two `replace_Znth` updates. Use permutation facts for swapping adjacent elements, preserve the already-sorted suffix because the swap occurs strictly before `n - i`, preserve cross-boundary ordering for the same reason, and prove that the element moved to `j + 1` is the maximum of the processed prefix.
- `entail_wit_4`: choose `l_outer = l_inner`. At inner-loop exit, `j = n - i - 1`, so the prefix-maximum fact gives that position `n - i - 1` is below every element in the old sorted suffix. Combining that with the old sorted suffix yields sortedness of the new suffix `sublist(n - (i + 1), n, l_inner)`.
- `return_wit_1`: choose `l0 = l_outer`. Since `i >= n` and the invariant also gives `i <= n`, conclude `i = n`, then `sublist(n - i, n, l_outer) = sublist(0, n, l_outer) = l_outer`; the stored sorted-suffix fact becomes the full-array sortedness needed for the postcondition. Permutation is already present.

## Likely helper lemmas

The witness proofs are mostly pure and should benefit from small helper lemmas for:

- `sorted_z nil`
- `sorted_z` on `sublist(0, Zlength l, l)`
- adjacent-swap permutation
- extending a sorted suffix by one boundary element using the cross-boundary ordering fact and the prefix-maximum fact

The plan is to add only the helper lemmas that compilation shows are actually necessary.

## Refinement

- 直接证明五个 witness 不够，需要先补最小辅助引理。
- 预计辅助引理包括：`sorted_z_nil`、`sublist_full`、相邻交换保持 `Permutation`、相邻交换不改变更右侧 `sublist`、以及把一个不大于后缀所有元素的边界元素接到已排序后缀前面仍保持 `sorted_z`。
- `entail_wit_1` 和 `entail_wit_2` 只需要 reflexive permutation、空后缀有序和 vacuous ordering。
- `entail_wit_3_1` 需要把交换后的列表选作 existential witness，并分别证明 permutation / suffix unchanged / cross-boundary unchanged / prefix-max 传播。
- `entail_wit_4` 需要由 `j + 1 >= n - i` 和 `j <= n - i - 1` 化出 `j = n - i - 1`，再用旧后缀有序和跨边界有序推出新后缀有序。
- `return_wit_1` 需要由 `i = n_pre` 把 `sublist (n_pre - i) n_pre l_outer` 改写成整个 `l_outer`。

## Progress

- 已证明：`entail_wit_1`、`entail_wit_2`、`return_wit_1`
- 未完成：`entail_wit_3_1`、`entail_wit_4`
- 当前剩余工作已经集中成两条 list-level bridge：
  - 相邻交换后的列表与原列表之间的 `Permutation/sublist` 关系
  - 由内层“前缀最大”事实推出外层“更长后缀有序”

## Iteration 2

- 已在 `proof_manual.v` 中补入 `replace_Znth` / `Znth` 的基础点值引理：
  - `replace_Znth_length`
  - `Znth_replace_Znth_eq`
  - `Znth_replace_Znth_other`
- 用这些基础引理后，`entail_wit_3_1` 的目标形状已经明确：选交换后的 `lswap` 作为 existential witness 是对的，剩余义务就是纯性质：
  - `Permutation l lswap`
  - `sorted_z (sublist (n_pre - i_2) n_pre lswap)`
  - 交换后前缀到后缀的跨边界有序
  - `j + 1` 位置成为新前缀 `[0..j+1]` 的最大值
- 本轮主要尝试把原列表分解为
  - `firstn (Z.to_nat j) l ++ Znth j l 0 :: Znth (j + 1) l 0 :: skipn (Z.to_nat (j + 2)) l`
  从而把交换后的列表化简成相邻交换的标准形状。
- 这个方向在 `coqtop` 中尚未完成，当前稳定卡点不是主 witness，而是分解引理本身：
  - `skipn (S (Z.to_nat j)) l` 与 `Znth (j + 1) l 0 :: skipn (Z.to_nat (j + 2)) l` 的改写没有直接对齐
  - 也就是说，当前缺的仍然是“相邻两元素分解”这一层辅助引理
- 对照现有例子可以确认：仓库里的排序题通常先在 `lib.v` 中准备好排序语义和关键引理，manual proof 只负责连接；当前 `bubble_sort` 没有对应的 `bubble_sort_lib`，所以证明成本集中落在 `manual.v` 里的这些桥接引理上。

## Iteration 3

- 已开始把辅助引理直接补进 `coq/generated/bubble_sort_proof_manual.v`，新增方向是：
  - `adjacent_swap_perm_z`
  - `adjacent_swap_suffix_unchanged`
- 当前 first blocker 已经从“缺少相邻交换理论”缩小为“`replace_Znth` 的第二层列表展开必须选对 `app_l/app_r`”。
- 通过 `coqtop` 检查可以确认：
  - 第一层把整表按前缀 `firstn (Z.to_nat j)` 与后缀 `x :: y :: tail` 分开时，使用 `replace_Znth_app_r` 是正确的。
  - 真正还未对齐的是随后对 `x :: y :: tail` 再做 `replace_Znth` 的那一步；这里不能机械继续用同一个改写方向，必须根据当前索引是在头元素还是尾部来选择 `replace_Znth_app_l` 或 `replace_Znth_app_r`。
- 所以当前没有退出 proof 阶段；下一轮的具体计划是：
  - 用 `coqtop` 把 `adjacent_swap_perm_z` 在第二层展开处的当前目标项完全打印出来；
  - 确认这一步是 `app_l` 还是 `app_r`；
  - 先把 `adjacent_swap_perm_z` 编译通过，再用它回填 `proof_of_bubble_sort_entail_wit_3_1`；
  - 随后用后缀不变与边界元素性质完成 `proof_of_bubble_sort_entail_wit_4`。

## Iteration 4

- 这一轮先不继续盲目改 `manual.v`，而是先回到 scratch proof，把 `adjacent_swap_perm_z` 的纯列表证明单独打通。
- 已确认一个具体失败原因：在主目标里全局 `rewrite <- Hzpref` 会把 `j` 改写进 `Z.to_nat j` 出现的位置，导致 `Hx` / `Hy` 虽然各自可证，但之后已经不能匹配主目标。
- 当前更稳的证明策略是：
  - 保持 `pref := firstn (Z.to_nat j) l`、`suf := skipn (S (Z.to_nat j)) l` 为局部记号；
  - 先把主目标中的两次 `Znth` 用局部断言 `Hx` / `Hy` 改写掉；
  - 之后只对 `replace_Znth` 的索引位置做局部 `replace (j ...) with (Zlength pref ...)`，避免全局改写污染 `pref` 的定义；
  - 最后再用 `swap_prefix_eq` 与 `perm_swap` 收尾。
- 这一轮的 first blocker 已经缩小成：在主目标里如何把 `Znth j ...` 和 `Znth (j+1) ...` 精确改写到 `pref ++ x :: y :: tail` 的形状，而不破坏 `pref` 里已有的 `Z.to_nat j`。
- 如果这一步在 scratch 里编译通过，就把 `swap_prefix_eq_nat`、`swap_prefix_eq`、新的 `adjacent_swap_perm_z` 直接搬进 `proof_manual.v`，然后继续回填 `entail_wit_3_1` 和 `entail_wit_4`。

## Iteration 5

- `adjacent_swap_perm_z` 已经在 scratch 中打通，并且稳定搬回 `proof_manual.v`。
- 为了让 `entail_wit_3_1` 不再在主 witness 里反复展开 `replace_Znth`，本轮补了 5 条直接服务于 bubble sort 的局部引理：
  - `adjacent_swap_Znth_j`
  - `adjacent_swap_Znth_j1`
  - `adjacent_swap_Znth_other`
  - `adjacent_swap_cross_order`
  - `adjacent_swap_prefix_max`
- 这组引理把“交换后的列表语义”拆成了三层：
  - 单点取值如何变化
  - 跨前缀/后缀的有序关系如何保持
  - 内层 invariant 里的 prefix-max 性质如何从 `j` 推进到 `j+1`
- `proof_of_bubble_sort_entail_wit_3_1` 已经编译通过。真正需要额外小心的点不是 list 理论本身，而是长度事实的来源：
  - 当前 heap 里拿到的是 `IntArray.full ... lswap`
  - 所以要先用 `IntArray.full_length` 得到 `length lswap = n_pre`
  - 再通过两次 `replace_nth_length` 折回 `length l_inner_2 = n_pre`
- 之后 `adjacent_swap_prefix_max` / `adjacent_swap_cross_order` / `adjacent_swap_suffix_unchanged` 的 side condition 才能闭合
- 当前只剩 `proof_of_bubble_sort_entail_wit_4` 未完成。下一轮先用 probe 看 `entailer!` 后的目标顺序，再决定是直接证明还是再补一个“把边界元素接到已排序后缀前仍有序”的辅助引理。

## Iteration 6

- `proof_of_bubble_sort_entail_wit_4` 已完成，`bubble_sort_proof_manual.v` 与 `bubble_sort_goal_check.v` 都已经编译通过。
- 本轮真正的阻塞点不是缺少新的排序语义，而是 4 个证明形状问题：
  - heap 目标 `&( "j") # Int |-> j |-- &( "j") # Int |->_` 不能手工重建 existential witness，直接使用库引理 `store_int_undef_store_int` 即可。
  - `sublist_single` 必须在把 `j + 1` 改写成 `n_pre - i` 之前使用，否则目标里不再出现 `sublist j (j + 1) ...` 的精确形状。
  - 新后缀有序最稳的目标形状是 `sorted_z (Znth j l_inner 0 :: sublist (n_pre - i) n_pre l_inner)`；这里直接应用 `sorted_z_cons_intro`，再把“头元素不大于后缀任意元素”单独证明，比继续对 `match` 目标做手工拆解更稳。
  - `Znth_sublist` 的 side condition 不能只靠 `lia`；需要先用 `sublist_length` 把 `q < Zlength (sublist ...)` 展开成 `q < hi - lo`，然后再重写。
- 到这一轮为止，五个 manual witness 全部闭合：
  - `entail_wit_1`
  - `entail_wit_2`
  - `entail_wit_3_1`
  - `entail_wit_4`
  - `return_wit_1`
