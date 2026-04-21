---
name: vc-checking
description: 在 Rocq MCP 中使用 tactics 检查分离逻辑验证条件（VC）是否满足。如果遇到问题，如何定位问题所在以及解决办法。
---

# VC 证明过程中的原则

1. VC 证明过程中只能修改对应的manual proof和C程序中的annotation，不能修改C程序的实现和生成的goal.v proof_auto.v和goal_check.v文件。

2. VC 证明过程中可以先通过分析结论是否可证来定位问题出在C程序annotation还是manual proof上。如果结论不可证，则说明问题出在annotation上；如果结论可证但证明过程中遇到困难，则说明问题出在manual proof上。

3. 每次修改了annotation之后，都需要重新运行symbolic execution到文件尾，获得最新完整witness列表。不要立刻运行symexec生成正式文件。

4. 每次重新运行symbolic execution或重新生成VC之后，都需要重新检查完整witness列表。manual VC的编号和内容可能变化，不能默认旧proof仍然对应当前VC。

5. 只检查和证明manual VC；auto-solved VC不需要导出、不需要手动证明。

6. 复用旧证明之前，必须确认当前VC与旧VC相同或仅有无关变量名变化；如果VC有实质变化，需要重新用rocq-mcp交互式跑通证明。

7. 所有qcp-mcp proof导出的manual VC都在临时Rocq文件中证明通过之后，才能运行symexec生成goal.v proof_auto.v proof_manual.v和goal_check.v文件，并把临时证明按VC主体匹配回填到proof_manual.v。

8. annotation中不能使用which implies和partial assertion，所有的annotation都应该是Assert或者Inv Assert开头的完整的断言。

9. 不能使用entailer! tactic进行证明。

10. 不能Import Logic.SeparationLogic.ProofTheory.SeparationLogic模块来使用derivable1相关的lemma来证明，如果遇到当前tactic解决不了的情况应该询问用户如何解决。

# VC 证明过程中的常见问题及解决办法

1. 如果遇到Znth相关的证明，应该参考SeparationLogic/listlib/README.md中的相关内容来进行证明。

2. 注意在使用split_pures之后的每个分支都必须要有一个dump_pre_spatial，否则会导致coqc卡死，然后出现segmentation fault
