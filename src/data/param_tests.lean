
import tactic
universes u v

inductive nat.param : ℕ → ℕ → Type
| zero : nat.param 0 0
| succ : Π (n0 n1 : ℕ), nat.param n0 n1 → nat.param (nat.succ n0) (nat.succ n1)

inductive rvec (α : Sort u) : ℕ → Type u
| nil {} : rvec nat.zero
| cons {n : ℕ} (vhd : rvec n) (vtl : α) : rvec n.succ

inductive rvec.param (α0 : Sort.{u}) (α1 : Sort.{u}) (αR : α0 -> α1 -> Sort.{u}) :
  Π (a0 : nat) (a1 : nat) (aR : nat.param a0 a1) (x0 : rvec.{u} α0 a0) (x1 : rvec.{u} α1 a1), Type.{u}
| nil : rvec.param nat.zero nat.zero nat.param.zero (rvec.nil.{u}) (rvec.nil.{u})
| cons (n0 : nat) (n1 : nat) (nR : nat.param n0 n1)
    (vhd0 : rvec.{u} α0 n0) (vhd1 : rvec.{u} α1 n1) 
    (vhdR : rvec.param n0 n1 nR vhd0 vhd1) /- this must be after vtl1, but why? -/
    (vtl0 : α0) (vtl1 : α1) (vtlR : αR vtl0 vtl1)
    :
  rvec.param (nat.succ n0) (nat.succ n1) (nat.param.succ n0 n1 nR)
    (rvec.cons.{u} vhd0 vtl0) (rvec.cons.{u} vhd1 vtl1)


inductive or.param : Π (a0 a1 : Prop), (a0 → a1 → Prop) →
  Π (b0 b1 : Prop), (b0 → b1 → Prop) → a0 ∨ b0 → a1 ∨ b1 → Prop
| inl : ∀ (a0 a1 : Prop) (aR : a0 → a1 → Prop) (b0 b1 : Prop) (bR : b0 → b1 → Prop) (h0 : a0) (h1 : a1),
  aR h0 h1 → or.param a0 a1 aR b0 b1 bR (or.inl h0) (or.inl h1)
| inr : ∀ (a0 a1 : Prop) (aR : a0 → a1 → Prop) (b0 b1 : Prop) (bR : b0 → b1 → Prop) (h0 : b0) (h1 : b1),
  bR h0 h1 → or.param a0 a1 aR b0 b1 bR (or.inr h0) (or.inr h1)

inductive false.param : false → false → Prop

def not.param : Π (a0 a1 : Prop), (a0 → a1 → Prop) → ¬a0 → ¬a1 → Prop :=
λ (a0 a1 : Prop) (aR : a0 → a1 → Prop) (f0 : a0 → false) (f1 : a1 → false),
  ∀ (a0 : a0) (a1 : a1), aR a0 a1 → false.param (f0 a0) (f1 a1)

axiom em.param : ∀ (p0 p1 : Prop) (pR : p0 → p1 → Prop),
  or.param p0 p1 pR (¬p0) (¬p1) (not.param p0 p1 pR) (classical.em p0) (classical.em p1)

example : false := 
begin
  rcases em.param true false (λ _ _, true)
    with ⟨_,_,_,_,_,_,_,f⟩ | ⟨_,_,_,_,_,_,tf⟩,
  {exact f}, {exact (tf true.intro)}
end

inductive nonempty.param : Π (α0 α1 : Sort u), (α0 → α1 → Sort v) → nonempty α0 → nonempty α1 → Prop
| intro (α0 α1 : Sort u) (αR : α0 → α1 → Sort v) (val0 : α0) (val1 : α1) : αR val0 val1 →
          nonempty.param α0 α1 αR (nonempty.intro val0) (nonempty.intro val1)

axiom choice.param (α0 α1 : Sort u) (αR : α0 → α1 → Sort v) (a0 : nonempty α0) (a1 : nonempty α1) :
    nonempty.param α0 α1 αR a0 a1 → αR (classical.choice a0) (classical.choice a1)

example : false :=
let R := nonempty.param bool bool (≠) in
let Rft : R ⟨ff⟩ ⟨tt⟩ := begin apply nonempty.param.intro, apply bool.ff_ne_tt end in
begin apply choice.param _ _ _ _ _ Rft, refl end

inductive in_closure (α : Type u) (mix : α → α -> α) : α → Prop
| basic (a : α) : in_closure a
| mul {a b : α} : in_closure a → in_closure b → in_closure (mix a b)
#print in_closure.rec

inductive in_closure.param (α0 : Type) (α1 : Type) (αR : α0 -> α1 -> Type) :
 Π (a0 : α0) (a1 : α1) (aR : αR a0 a1)
   (x0 : in_closure α0 a0) (x1 : in_closure α1 a1), Prop
| basic (a0 : α0) (a1 : α1) (aR : αR a0 a1) :
  (in_closure.param a0 a1 aR (in_closure.basic a0)
   (in_closure.basic a1))
| mul (a0 : α0) (a1 : α1) (aR : αR a0 a1) 
      (a0_1 : in_closure α0 a0) (a1_1 : in_closure α1 a1)
      (aR_1 : in_closure.param a0 a1 aR a0_1 a1_1) 
      (a0_2 : in_closure α0 a0) (a1_2 : in_closure α1 a1) 
      (aR_1 : in_closure.param a0 a1 aR a0_2 a1_2) :
      (in_closure.param a0 a1 aR 
      (in_closure.mul a0_1 a0_2) (in_closure.mul a1_1 a1_2))
