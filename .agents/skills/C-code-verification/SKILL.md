---
name: C-code-verification
description: C代码验证技能。当用户需要检查C代码是否正确的时候使用。 
---

# C 代码验证流程

执行以下步骤来检查并验证C代码的正确性：

## 第一步：代码审查
检查代码是否有最基本的function specifications描述，确保每个函数都有明确的输入输出说明。

## 第二步：Invariant补充和符号执行检查（参考 `annotation-and-symbolic-execution` skill）

根据代码的功能和逻辑，补充必要的loop invariant, 所有的loop invariant都应该满足以下条件：
- 以Inv Assert形式给出完整的invariant

也许你需要一些额外的断言来辅助符号执行，这些断言也必须以Assert的形式给出，不能使用除where以外的其它feature来提供annotation。

然后通过qcp-mcp来进行代码验证，保证能够通过语法检查和符号执行。
在代码验证之前你需要更新文件长度的信息，确保符号执行能够正确地进行到文件尾部。

验证过程中如果发现错误，需要根据错误提示进行修正，直到能够通过验证。
如果需要修改C代码需要暂停验证，与用户讨论修改方案，确保修改后的代码能够满足功能需求并且能够通过验证。

## 第三步：Rocq检查（参考 `vc-proving`, `vc-checking` skill）

符号执行检查过程中会打印一些待证明的witness, 这些witness需要在Rocq中使用rocq-mcp进行证明，确保所有的witness都能够被证明为正确。你需要symbolic到文件尾来获得完整的witness列表，如果你有对文件进行修改(比如补充了invariant或者是Coq定义)，需要重新symbolic来获得最新的witness列表，注意你每次修改之后文件尾所在的行数就发生改变了。

每次重新symbolic之后，都必须把新的完整witness列表当作当前事实来源，重新检查manual witness的编号和内容。之前证明过的VC也要检查是否变化；如果没有变化，可以保留已有proof，不需要重新copy；如果发生实质变化，必须重新证明。auto-solved的VC不需要导出、不需要手动证明。

对于一个生成的witness，在Rocq证明之前你可以进行简单的分析，每个witness都是``P |-- Q``的形式，你可以分析一下P和Q分别是什么，看看它们之间的关系是什么，看看它们是否能够被证明为正确，这样对于错误的witness你就可以直接拒绝掉然后去审查代码和invariant，找出问题所在并进行修正。

如果发现无法证明的witness，需要重新审查代码和invariant，找出问题所在并进行修正，直到所有的witness都能够被证明为正确。

证明witness的时候请依次使用qcp-mcp的proof打印出对应的witness到Rocq中，证明结束之后再进行下一个的证明。manual VC必须按“导出一个、分析一个、用rocq-mcp交互式证明一个、保存一个”的节奏处理，不要一次性导出很多VC后跳着证明。

所有qcp-mcp proof导出的manual VC都在临时Rocq文件中证明通过之后，才能执行symexec生成正式goal, proof_auto, proof_manual和goal_check文件。symexec不是manual VC证明的起点；它是临时证明全部跑通后的正式文件生成步骤。回填正式proof_manual.v时，需要按VC主体形状匹配，不要只相信witness编号。

证明的过程中可以补充必要的辅助引理和定义，以便更容易地完成证明，你可以通过Coq中Search tactic来查找相关可以使用的引理。但是你不能在证明过程中引入Axioms, 你可以通过rocq-mcp的rocq-verify来检查是否引入了Axioms。

在这一步中你不能使用除了qcp-mcp/rocq-mcp之外的工具来进行证明。

## 第四步：总结

在完成以上步骤之后，你需要总结整个验证过程。

你需要在所有qcp-mcp proof导出的manual VC都证明通过之后，执行symexec来生成goal, proof_auto, proof_manual等文件，并把已经跑通的witness证明按VC主体匹配填入proof_manual.v中，最后编译完成所有生成的文件。

是否完成的标准有两点：
- proof_manual.v中没有Admitted的证明也没有Axioms的引入。
- proof_check.v文件能够成功编译。

然后删除所有临时文件，注意在删除的时候要把之前的Rocq文件编译产生的.aux文件也删除掉。

注意最后用symexec生成的几个文件不需要删除。
