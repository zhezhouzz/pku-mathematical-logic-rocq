(** * 教材习题二（pp. 98--104）

    本文件按教材编号组织。证明题以 [Goal ... Abort.] 保留给学生；
    计算题可以逐句执行 [Compute]。第 1、5--8、21--28、30--32 题
    主要是自然语言符号化、函数完全集、范式或开放讨论题，列在相应
    注释中，不伪装成已经证明的 Rocq 定理。 *)

From Stdlib Require Import String List Bool.
From stdpp Require Import gmap.
From LogicCourse.Propositional Require Import
  Syntax Semantics NaturalDeduction DerivedRules Hilbert.

Open Scope string_scope.
Open Scope N_scope.

Definition ep : formula := Atom "p".
Definition eq : formula := Atom "q".
Definition er : formula := Atom "r".
Definition pA : pformula := PAtom "A".
Definition pB : pformula := PAtom "B".
Definition pC : pformula := PAtom "C".

(** 1. 将六个自然语言命题符号化：否定合取、析取、充分条件、
    必要条件、"除非"以及奇偶性充要条件。课堂上先确定原子命题。 *)

(** 2. 写真值表。 *)
Compute printTruthTable ((¬ ep) ∧ (¬ eq)).
Compute printTruthTable ((ep → eq) → er).
Compute printTruthTable (ep → (eq → er)).
Compute printTruthTable ((ep → (eq → er)) → ((ep → eq) → (ep → er))).

(** 3. 求所有成真指派，并分类为重言式、矛盾式或可满足式。 *)
Compute printTruthTable (ep → (eq → ep)).
Compute printTruthTable ((eq ∨ er) → ((¬ er) → eq)).
Compute printTruthTable (ep → (ep ∨ eq)).
Compute printTruthTable ((ep ∧ (¬ ep)) → eq).
Compute printTruthTable ((ep ∨ (¬ ep)) → eq).
Compute printTruthTable ((ep ∨ (¬ ep)) → ((eq ∨ (¬ eq)) → er)).
Compute printTruthTable (((ep → eq) ∧ (eq → er)) → (ep → er)).
Compute printTruthTable ((¬ (ep → eq)) ∧ eq).

(** 4. 用真值表检查两式确定同一真值函数。 *)
Example ex2_4 :
  isValid (((¬ ep) → (eq ∨ er)) ↔ ((¬ (((¬ eq) → er))) → ep)) = true.
Proof. reflexivity. Qed.

(** 5--8. 真值函数表示以及 NAND/NOR 单联结词完备性，适合作为纸笔题。 *)
(** 9--10. 补全例 2.15(1)(3) 与例 2.16(2)(3)(6) 的 N 证明。 *)

Definition n_equivalent (A B : formula) : Prop :=
  (({[A]} : Context) ⊢ₙ B) /\ (({[B]} : Context) ⊢ₙ A).

Section NExercises.
  Variables A B C D E T : formula.

  (** 11. 六组经典等值式。 *)
  Goal n_equivalent (A ∨ (B ∧ C)) ((A ∨ B) ∧ (A ∨ C)). Abort.
  Goal n_equivalent (A ∧ (B ∨ C)) ((A ∧ B) ∨ (A ∧ C)). Abort.
  Goal n_equivalent (A → (B ∧ C)) ((A → B) ∧ (A → C)). Abort.
  Goal n_equivalent (A → (B ∨ C)) ((A → B) ∨ (A → C)). Abort.
  Goal n_equivalent ((A ∧ B) → C) ((A → C) ∨ (B → C)). Abort.
  Goal n_equivalent ((A ∨ B) → C) ((A → C) ∧ (B → C)). Abort.

  (** 12. 关于双条件的十一题。 *)
  Goal ({[A ↔ B; A]} : Context) ⊢ₙ B. Abort.
  Goal ({[A ↔ B; B]} : Context) ⊢ₙ A. Abort.
  Goal n_equivalent (A ↔ B) (B ↔ A). Abort.
  Goal n_equivalent (¬ (A ↔ B)) ((¬ A) ↔ B). Abort.
  Goal n_equivalent (¬ (A ↔ B)) (A ↔ (¬ B)). Abort.
  Goal n_equivalent (A ↔ B) (((¬ A) ∨ B) ∧ (A ∨ (¬ B))). Abort.
  Goal n_equivalent (A ↔ B) ((A ∧ B) ∨ ((¬ A) ∧ (¬ B))). Abort.
  Goal n_equivalent ((A ↔ B) ↔ C) (A ↔ (B ↔ C)). Abort.
  Goal ({[A ↔ B; B ↔ C]} : Context) ⊢ₙ (A ↔ C). Abort.
  Goal ({[A ↔ (¬ A)]} : Context) ⊢ₙ B. Abort.
  Goal (∅ : Context) ⊢ₙ ((A ↔ B) ∨ (A ↔ (¬ B))). Abort.

  (** 13. 有前提的综合证明。 *)
  Goal ({[A → (B → C); A ∧ B]} : Context) ⊢ₙ C. Abort.
  Goal ({[(¬ A) ∨ B; ¬ (B ∧ C); C]} : Context) ⊢ₙ (¬ A). Abort.
  Goal ({[A → B]} : Context) ⊢ₙ (A → (A ∧ B)). Abort.
  (** 13(4) 严格照扫描本录入。原书的结论含 [A]，但前提中没有
      能推出 [A] 的公式；例如令 [A] 假、[B,C,D,E] 真即可构成反例。
      这很可能是原书排印遗漏，适合让学生先检查题目是否成立。 *)
  Goal ({[B → D; B ↔ C; D ↔ E; E ∧ C]} : Context) ⊢ₙ
    (A ∧ B ∧ C ∧ D).
  Abort.
  Goal ({[A → (A → B)]} : Context) ⊢ₙ ((¬ B) → (¬ A)). Abort.
  Goal ({[A → B; (¬ (B → C)) → (¬ A)]} : Context) ⊢ₙ (A → C). Abort.
  Goal ({[(A → B) → A]} : Context) ⊢ₙ A. Abort.
  Goal ({[(A → B) → C]} : Context) ⊢ₙ (A ∨ C). Abort.
  (** 13(9) 也按原书录入；令 [A,B] 真、[C] 假即为反例，疑为排印错误。 *)
  Goal ({[(A → B) → A]} : Context) ⊢ₙ ((¬ B) ∨ C). Abort.
  Goal ({[¬ (A → B)]} : Context) ⊢ₙ (B → A). Abort.
  Goal ({[(¬ A) ∨ B; ¬ B]} : Context) ⊢ₙ (¬ A). Abort.
  Goal ({[A ∧ B; (¬ B) ∨ C]} : Context) ⊢ₙ (A ∧ C). Abort.
  Goal ({[A → (¬ B); B ∨ (¬ C); C ∧ (¬ D)]} : Context) ⊢ₙ (¬ A). Abort.
  Goal ({[A ∨ B; A → C; B → D]} : Context) ⊢ₙ (C ∨ D). Abort.
  Goal ({[(A ∨ B) → (C ∧ D); (D ∨ E) → T]} : Context) ⊢ₙ (A → T). Abort.
  Goal ({[A ∨ B; B → C; A → D; ¬ D]} : Context) ⊢ₙ ((A ∨ B) ∧ C). Abort.
End NExercises.

Open Scope P_scope.

Section PExercises.
  Variables A B C D : pformula.

  (** 14. 直接写出四个 P 证明序列。 *)
  Goal (∅ : PContext) ⊢ₚ ((A → B) → ((¬ A → ¬ B) → (B → A))). Abort.
  Goal (∅ : PContext) ⊢ₚ
    (((A → (B → C)) → (A → B)) → ((A → (B → C)) → (A → C))). Abort.
  Goal (∅ : PContext) ⊢ₚ ((A → (A → B)) → (A → B)). Abort.
  Goal (∅ : PContext) ⊢ₚ (A → (B → (A → B))). Abort.

  (** 15. 有前提的 P 证明序列。 *)
  Goal ({[A → B; (¬ (B → C)) → (¬ A)]} : PContext) ⊢ₚ (A → C). Abort.
  Goal ({[A → (B → C)]} : PContext) ⊢ₚ (B → (A → C)). Abort.
  Goal ({[¬ (A → B)]} : PContext) ⊢ₚ A. Abort.
  Goal ({[¬ (A → B)]} : PContext) ⊢ₚ (¬ B). Abort.

  (** 16. 用演绎定理证明三个内定理。 *)
  Goal (∅ : PContext) ⊢ₚ (((¬ (A → B)) → C) → (A → ((¬ B) → C))). Abort.
  Goal (∅ : PContext) ⊢ₚ ((A → (B → (¬ A))) → (A → (¬ B))). Abort.
  Goal (∅ : PContext) ⊢ₚ ((((¬ A) → B) → C) → (A → C)). Abort.

  (** 17. 三个前提变换问题。 *)
  Goal ({[(A → B) → B]} : PContext) ⊢ₚ ((B → A) → A). Abort.
  Goal ({[(A → B) → C]} : PContext) ⊢ₚ ((A → C) → C). Abort.
  Goal ({[(A → B) → C]} : PContext) ⊢ₚ ((D → A) → (D → C)). Abort.

  (** 18--20 要求把第 11--13 题改写为 P 的缩写联结词后证明。 *)

End PExercises.

(** 21--24：赋值刻画、等值的同余性和代换保持重言式。
    25--26：求析取范式、合取范式。
    27：由书中推论 2.10 推定理 2.30。
    28：证明 P 的可靠性。 *)

(** 29. 判断下列公式是否为 P 的内定理。先跑真值表作语义检查，
    随后对有效式构造 P 证明，对无效式写出反指派。 *)
Compute isValid (p_to_n ((pA → (¬ pA)) → (¬ pA))).
Compute isValid (p_to_n (((¬ pA) → pB) → (pA → (¬ pB)))).
Compute isValid (p_to_n (((¬ pB) → pA) → (pA → (¬ pB)))).
Compute isValid (p_to_n ((¬ (pA → pB)) → (¬ pB))).
Compute isValid (p_to_n (pA → (pB → (¬ (pA → pB))))).
Compute isValid (p_to_n (pA → (pB → (¬ (pA → (¬ pB)))))).
Compute isValid (p_to_n ((pA → pB) → ((pC → pA) → (pC → pB)))).
Compute isValid
  (p_to_n ((pA → pB) → (((pC → (¬ pA))) → (pC → (¬ pB))))).

(** 30--32：讨论改变 N/P 的规则或公理后得到的等价与弱等价系统。 *)
