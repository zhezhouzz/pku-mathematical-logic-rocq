# 北大数理逻辑课：Rocq 教学实现

这是一个面向课堂的、小型 deep embedding，内容暂时对应王捍贫老师教材的前三章。设计目标是让学生看见公式、语义和证明树本身，而不是尽早进入复杂元理论。

## 内容

- `Propositional/Syntax.v`：命题公式、复杂度、深度、变元集；
- `Propositional/Semantics.v`：赋值、真值表、有效式、可满足式和 `Γ ⊨ A`；
- `Propositional/NaturalDeduction.v`：自然演绎系统 N；
- `Propositional/DerivedRules.v`：N 中常用的导出规则及示范证明；
- `Propositional/Hilbert.v`：只含 `¬`、`→` 的 Hilbert 系统 P；
- `Tactics.v`：集合/context 的课堂用规范化 tactic；
- `FirstOrder/Syntax.v`：项、公式、自由变量、可代入条件和代换；
- `FirstOrder/Semantics.v`：Tarski 语义；
- `FirstOrder/NaturalDeduction.v`：系统 `N_L`；
- `FirstOrder/Hilbert.v`：系统 `K_L`；
- `Examples/`：可以逐句运行的课堂演示；
- `Exercises/Chapter2.v`、`Exercises/Chapter3.v`：按教材习题二、三编号整理的学生 worksheet；
- [`TEXTBOOK_COVERAGE.md`](TEXTBOOK_COVERAGE.md)：教材章节、定理和 Rocq 文件的逐项对照。

N、P、`N_L`、`K_L` 都提供了结构性元定理，而不只是原始推理规则。尤其可以直接
使用 `N_weaken`、`P_weaken`、`NL_weaken`、`K_weaken`，以及相应的
`N_cut`、`P_cut`、`NL_cut`、`K_cut`；P 和 K 还包含教材的演绎定理。

上下文和变元集都使用 stdpp 的 `gset`。N、P、`N_L`、`K_L` 使用不同的判断符号；N、P 和一阶公式的联结词也分别放在 `N_scope`、`P_scope`、`FOL_scope` 中，因此可以复用自然的 `¬`、`∧`、`∨`、`→`、`↔`。Rocq 已占用裸的 `∀`、`∃` 作为元语言 binder，所以对象语言量词写作 `∀ₒ`、`∃ₒ`。

## 构建

本机已有的 `with-rocq-1` opam switch 包含 Rocq 9.1、Dune 和 `rocq-stdpp`：

```sh
cd /Users/zhezhou/Documents/Projects/pku-mathematical-logic-rocq
make build
```

`make build` 根据 `_RocqProject` 生成依赖关系并编译全部 `.v` 文件。

## 在编辑器中逐句执行

`make build` 已经把 VsRocq 需要的 `.vo` 文件放在源码对应目录。如果第一次打开编辑器前还没有构建，也可以执行同义的：

```sh
make ide
```

它根据 `_RocqProject` 编译出编辑器能够找到的 `.vo` 文件。源码改变后可以再次运行 `make ide`。

用 VS Code/Cursor **单独打开本项目目录**，并让 Rocq 插件使用 `with-rocq-1` switch 中的 `vsrocqtop`。在 `.v` 文件中把光标放到某条命令上，用插件的 **Interpret to Point** 前进到光标位置；用 **Step Forward** / **Step Backward** 逐句前进或后退。可以先打开：

- `theories/Examples/TruthTables.v`；
- `theories/Examples/NProofs.v`；
- `theories/Examples/PProofs.v`。

例如：

```rocq
Open Scope N_scope.

Example identity (A : formula) : (∅ : Context) ⊢ₙ (A → A).
Proof.
  apply N_impIntro.
  n_assumption.
Qed.
```

这里 `N_impIntro` 就是蕴含引入规则。四套系统中，rule 的 context、公式、
项和变元索引都设为隐式；Rocq 可以从目标以及随后提供的证明参数中恢复它们：

```rocq
apply N_impIntro.                    (* Γ、A、B 由目标给出 *)
exact (N_impElim lineAB lineA).      (* A 由两个证明参数给出 *)
exact (N_conjElimLeft lineAB).       (* B 由 lineAB : Γ ⊢ₙ A ∧ B 给出 *)
apply (N_disjElim (A := A) (B := B)). (* apply 时尚无证明参数，故命名中间公式 *)
```

当 `apply` 尚不能约束某个隐式参数时，使用命名参数，例如
`N_impElim (A := A)`。系统 N 的规则统一以 `N_` 开头，
系统 P 以 `P_` 开头；`About N_impElim.` 会同时显示完整类型和 `Arguments` 声明。

集合形式可以统一化简：

```rocq
normalize_context.                         (* 去掉 ∅、相邻重复项并统一括号 *)
normalize_context_to ({[A; B]} : Context). (* 用 set_solver 换成指定的等价形式 *)
```

真值表是一个 record；`printTruthTable` 返回适合展示的字符串列表，因此可以直接逐句执行：

```rocq
Compute printTruthTable (Imp (Atom "p") (Atom "p")).
```

`Γ ⊨ A` 是语义后承：它检查（命题逻辑）或陈述（一阶逻辑）每一个使 `Γ` 中所有前提为真的解释是否也使 `A` 为真。它不同于 `Γ ⊢ₙ A`：前者谈语义，后者是一棵按照系统 N 规则构造出的证明树。
