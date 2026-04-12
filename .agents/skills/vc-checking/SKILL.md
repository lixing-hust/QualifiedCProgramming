---
name: vc-checking
description: 在 Rocq MCP 中使用 tactics 检查分离逻辑验证条件（VC）是否满足。如果遇到问题，如何定位问题所在以及解决办法。
---

# VC 证明过程中的原则

1. VC 证明过程中只能修改对应的manual proof和C程序中的annotation，不能修改C程序的实现和生成的goal.v proof_auto.v和goal_check.v文件。

2. VC 证明过程中可以先通过分析结论是否可证来定位问题出在C程序annotation还是manual proof上。如果结论不可证，则说明问题出在annotation上；如果结论可证但证明过程中遇到困难，则说明问题出在manual proof上。

3. 每次修改了annotation之后，都需要重新生成goal.v proof_auto.v和goal_check.v文件，并重新进行编译，再进行VC证明。

4. annotation中不能使用which implies和partial assertion，所有的annotation都应该是Assert或者Inv Assert开头的完整的断言。

5. 如果发现，goal.v已经修改但是VC证明过程中的结论没有变化，需要停下来询问用户是否相关文件被正常修改和编译。

6. 不能使用entailer! tactic进行证明。

7. 不能Import Logic.SeparationLogic.ProofTheory.SeparationLogic模块来使用derivable1相关的lemma来证明，如果遇到当前tactic解决不了的情况应该询问用户如何解决。

# VC 证明过程中的常见问题及解决办法

