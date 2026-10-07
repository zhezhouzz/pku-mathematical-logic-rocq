# 《数理逻辑（离散数学一分册）》前三章对应表

本项目以“学生能看懂并能亲手调用规则”为第一目标。下表区分三类内容：

- **已实现**：有可编译的定义或定理证明；
- **学生练习**：在 worksheet 中以 `Goal ... Abort.` 留空；
- **纸笔/后续**：保留教材编号和任务说明，但暂不引入复杂自动化或元理论。

## 第二章：命题逻辑

| 教材内容 | Rocq 文件 | 状态 |
|---|---|---|
| 2.1 公式、复杂度、深度、变元 | `Propositional/Syntax.v` | 已实现 |
| 2.2 指派、真值表、重言式、可满足式、语义后承 | `Propositional/Semantics.v` | 已实现，可计算 |
| 2.3 完全联结词集 | `Propositional/Hilbert.v`、`Exercises/Chapter2.v` 第 5–8 题 | P 中的缩写已实现；完整性证明保留为纸笔题 |
| 2.4 形式推演 | N/P 的 `...Derivation` 归纳定义 | 已实现 |
| 2.5 系统 N | `Propositional/NaturalDeduction.v` | 全部规则；定理 2.5 增加前提律 `N_weaken`；定理 2.6 传递律 `N_substitution` / `N_cut` |
| 2.5 常用导出规则 | `Propositional/DerivedRules.v` | 同一律、爆炸律、双重否定、反证、拒取式、蕴含传递、交换律等 |
| 2.6 系统 P | `Propositional/Hilbert.v` | A1–A3、MP、`P_identity`、`P_weaken`、定理 2.10 演绎定理、定理 2.11 逆定理、传递/cut |
| 2.7 N 与 P 的等价 | worksheet 中保留相关任务 | 双向翻译与总等价定理尚未加入核心库 |
| 2.8–2.10 赋值刻画、可靠性与完备性 | `Semantics.v` 与 `Chapter2.v` 第 21–28 题 | 计算语义已实现；复杂元理论按课程最初的简化目标暂作高阶练习 |
| 习题二（教材 pp. 98–104） | `Exercises/Chapter2.v` | 按 1–32 题编号恢复；可形式化的子题写成可执行计算或 Rocq goal |

## 第三章：一阶逻辑

| 教材内容 | Rocq 文件 | 状态 |
|---|---|---|
| 3.1 符号化 | `Exercises/Chapter3.v` 第 1–2 题 | 纸笔练习 |
| 3.2 项、公式、自由变元、代换 | `FirstOrder/Syntax.v` | 已实现，可计算 |
| 3.3 系统 N_L | `FirstOrder/NaturalDeduction.v` | 全部命题及量词规则；增加前提律 `NL_weaken`；定理 3.2(1) 的单公式传递形式 `NL_cut` / `NL_transitivity` |
| 3.3 前束范式 | `Chapter3.v` 第 17–19 题 | 保留题目；暂不加入会遮蔽证明思想的自动前束化算法 |
| 3.4 系统 K_L | `FirstOrder/Hilbert.v` | K1–K7、MP、`K_identity`、`K_weaken`、全称推广、定理 3.8 演绎定理、传递/cut |
| 3.5 N_L 与 K_L 的等价 | worksheet 中保留相关任务 | 双向总等价定理尚未加入核心库 |
| 3.6–3.9 语义、可靠性、和谐性与完备性 | `FirstOrder/Semantics.v` 与 `Chapter3.v` 第 22–32 题 | Tarski 语义已实现；复杂元理论保留为后续单元 |
| 习题三（教材 pp. 183–187） | `Exercises/Chapter3.v` | 按 1–32 题编号恢复；可形式化的子题写成 Rocq goal |

## 使用方式

教师可直接展示 `NaturalDeduction.v` / `Hilbert.v` 中已经证明的元定理；学生在
`Exercises/Chapter2.v` 和 `Exercises/Chapter3.v` 中把某个 `Abort` 改成
`Proof. ... Qed.`。这样同一份代码同时保留“规则库”和“无答案练习册”，又不会把
可靠性、完备性等较重内容提前塞进基础课堂。
