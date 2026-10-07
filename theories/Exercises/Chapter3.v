(** * 教材习题三（pp. 183--187）

    与第二章 worksheet 相同：证明题保留为 [Abort]，语法计算可以
    逐句执行。模型构造、前束范式计算和开放讨论题保留教材编号与
    任务说明，供纸笔作业或以后扩展自动化。 *)

From Stdlib Require Import String List Bool.
From stdpp Require Import gmap.
From LogicCourse.FirstOrder Require Import
  Syntax Semantics NaturalDeduction Hilbert.

Import ListNotations.
Open Scope string_scope.
Open Scope FOL_scope.

(** 1. 将十二个数学命题表示为一阶公式，并明确非逻辑符号集。
    2. 用一阶语言描述偏序关系。 *)

(** 3--5. 自由/约束出现、代换、闭公式。这里提供同类可运行实例。 *)
Definition ex_x1 : term := Var "x1".
Definition ex_x2 : term := Var "x2".
Definition ex_x3 : term := Var "x3".
Definition ex_t : term := Func "f" [ex_x1; ex_x2].
Definition ex_A : formula :=
  Forall "x2" (Imp (Rel "F" [ex_x1; ex_x2]) (Rel "G" [ex_x3])).

Compute elements (free_variables ex_A).
Compute substitute "x1" ex_t ex_A.
Compute free_for ex_t "x1" ex_A.
Compute is_sentence ex_A.

Section NLExercises.
  Variables Γ : Context.
  Variables A A' B C : formula.
  Variables x y : string.

  (** 6. 改名：若 y 对 x 在 A 中自由，则 ∀xA ⊢ ∀y A(x/y)。 *)
  Goal free_for (Var y) x A = true ->
    ({[Forall x A]} : Context) ⊢ₙₗ Forall y (substitute x (Var y) A).
  Abort.

  (** 7. 存在量词与否定全称量词。 *)
  Goal ({[Exists x A]} : Context) ⊢ₙₗ Neg (Forall x (Neg A)). Abort.

  (** 8. 等值替换到全称量词下。 *)
  Goal ({[Iff A A']} : Context) ⊢ₙₗ Iff (Forall x A) (Forall x A'). Abort.

  (** 9. 补全例 3.12(2)(3)(4)：量词与 ∧/∨ 的移出规则。 *)
  Goal x ∉ free_variables A ->
    ({[Conj A (Exists x B)]} : Context) ⊢ₙₗ Exists x (Conj A B).
  Abort.
  Goal x ∉ free_variables A ->
    ({[Disj A (Forall x B)]} : Context) ⊢ₙₗ Forall x (Disj A B).
  Abort.
  Goal x ∉ free_variables A ->
    ({[Disj A (Exists x B)]} : Context) ⊢ₙₗ Exists x (Disj A B).
  Abort.

  (** 10--13. 把一个推演提升到量词前提/结论。 *)
  Goal ({[A]} ∪ Γ) ⊢ₙₗ B -> ({[Forall x A]} ∪ Γ) ⊢ₙₗ B. Abort.
  Goal (forall D, D ∈ Γ -> x ∉ free_variables D) ->
    ({[A]} ∪ Γ) ⊢ₙₗ B ->
    ({[Forall x A]} ∪ Γ) ⊢ₙₗ Forall x B.
  Abort.
  Goal ({[A]} ∪ Γ) ⊢ₙₗ B ->
    ({[Exists x A]} ∪ Γ) ⊢ₙₗ Exists x B.
  Abort.
  Goal (forall D, D ∈ Γ -> x ∉ free_variables D) ->
    ({[A]} ∪ Γ) ⊢ₙₗ B ->
    ({[Exists x A]} ∪ Γ) ⊢ₙₗ Forall x B.
  Abort.

  (** 14. 五个 N_L 量词证明。 *)
  Goal ({[Forall x A]} : Context) ⊢ₙₗ Exists x A. Abort.
  Goal ({[Forall x (Imp A B); Exists x A]} : Context) ⊢ₙₗ
    Exists x (Conj A B).
  Abort.
  Goal ({[Forall x (Iff A B); Forall x (Iff B C)]} : Context) ⊢ₙₗ
    Forall x (Iff A C).
  Abort.
  Goal ({[Exists x (Exists y A)]} : Context) ⊢ₙₗ Exists y (Exists x A). Abort.
  Goal ({[Exists x (Forall y A)]} : Context) ⊢ₙₗ Forall y (Exists x A). Abort.

  (** 15. Q1/Q2 分别取 ∀ 或 ∃，练习把量词移过 ∧ 与 ∨。 *)
  Goal x ∉ free_variables B -> y ∉ free_variables A ->
    ({[Conj (Forall x A) (Exists y B)]} : Context) ⊢ₙₗ
      Forall x (Exists y (Conj A B)).
  Abort.
  Goal x ∉ free_variables B -> y ∉ free_variables A ->
    ({[Disj (Exists x A) (Forall y B)]} : Context) ⊢ₙₗ
      Exists x (Forall y (Disj A B)).
  Abort.

  (** 16. 判断由 Γ ⊢ A→B 能否推出
      Γ ⊢ ∀xA→∀xB，以及 Γ ⊢ ∃xA→∃xB；需要明确新鲜性条件。 *)
End NLExercises.

(** 17. 求四式的前束范式。
    18. 求四式的 Π 型前束范式。
    19. 求三式的 Σ 型前束范式。
    当前核心库保留具名变量的初学者语法，前束化算法将在独立模块加入。 *)

Section KExercises.
  Variables Γ : Context.
  Variables A B C : formula.
  Variable x : string.

  (** 20. 在 K_L 中证明。 *)
  Goal (∅ : Context) ⊢ₖ
    (Disj (Exists x A) (Exists x B) → Exists x (Disj A B)). Abort.
  Goal (∅ : Context) ⊢ₖ
    (Disj (Forall x A) (Forall x B) → Forall x (Disj A B)). Abort.
  Goal (∅ : Context) ⊢ₖ
    (Exists x (Conj A B) → Conj (Exists x A) (Exists x B)). Abort.
  Goal (∅ : Context) ⊢ₖ
    (Forall x (Conj A B) ↔ Conj (Forall x A) (Forall x B)). Abort.
  Goal (∅ : Context) ⊢ₖ
    (Forall x (A → B) → (Forall x (B → C) → Forall x (A → C))). Abort.
  Goal (∅ : Context) ⊢ₖ
    (Disj (Exists x A) (Forall x B) → (Forall x (Neg A) → Forall x B)). Abort.

  (** 21. 四个带新鲜性条件的量词移动公式。 *)
  Goal x ∉ free_variables B -> (∅ : Context) ⊢ₖ
    (Exists x (A → B) → (Forall x A → B)). Abort.
  Goal x ∉ free_variables B -> (∅ : Context) ⊢ₖ
    ((Forall x A → B) → Exists x (A → B)). Abort.
  Goal x ∉ free_variables A -> (∅ : Context) ⊢ₖ
    (Exists x (A → B) → (A → Exists x B)). Abort.
  Goal x ∉ free_variables A -> (∅ : Context) ⊢ₖ
    ((A → Exists x B) → Exists x (A → B)). Abort.
End KExercises.

(** 22--23. 在给定整数/自然数解释下计算满足指派和公式真值。
    24--25. 证明指定公式永真。
    26--29. 判断关于蕴含、量词和语义后承的命题并给出反例。
    30. 构造给定解释的极大和谐公式集。
    31. 比较加入公式与加入其全称闭式后的和谐性。
    32. 讨论删去 N_L 的增加前提律后，形式定理和内定理的变化。 *)
