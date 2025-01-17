/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro

Tensor product of modules over commutative rings.

-/

import group_theory.free_abelian_group
import linear_algebra.basic tactic.squeeze

variables {R : Type*} [comm_ring R]
variables {M : Type*} {N : Type*} {P : Type*} {Q : Type*}
variables [add_comm_group M] [add_comm_group N] [add_comm_group P] [add_comm_group Q]
variables [module R M] [module R N] [module R P] [module R Q]
include R

set_option class.instance_max_depth 100

namespace linear_map

def mk₂ (f : M → N → P)
  (H1 : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
  (H2 : ∀ c m n, f (c • m) n = c • f m n)
  (H3 : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
  (H4 : ∀ c m n, f m (c • n) = c • f m n) : M →ₗ N →ₗ P :=
⟨λ m, ⟨f m, H3 m, λ c, H4 c m⟩,
λ m₁ m₂, linear_map.ext $ H1 m₁ m₂,
λ c m, linear_map.ext $ H2 c m⟩

@[simp] theorem mk₂_apply
  (f : M → N → P) {H1 H2 H3 H4} (m : M) (n : N) :
  (mk₂ f H1 H2 H3 H4 : M →ₗ N →ₗ P) m n = f m n := rfl

variables (f : M →ₗ N →ₗ P)

theorem ext₂ {f g : M →ₗ N →ₗ P}
  (H : ∀ m n, f m n = g m n) : f = g :=
linear_map.ext (λ m, linear_map.ext $ λ n, H m n)

def flip : N →ₗ M →ₗ P :=
mk₂ (λ n m, f m n)
  (λ n₁ n₂ m, (f m).map_add _ _)
  (λ c n m, (f m).map_smul _ _)
  (λ n m₁ m₂, by rw f.map_add; refl)
  (λ c n m, by rw f.map_smul; refl)

@[simp] theorem flip_apply (m : M) (n : N) : flip f n m = f m n := rfl

theorem flip_inj {f g : M →ₗ N →ₗ P} (H : flip f = flip g) : f = g :=
ext₂ $ λ m n, show flip f n m = flip g n m, by rw H

variables (R M N P)
def lflip : (M →ₗ N →ₗ P) →ₗ N →ₗ M →ₗ P :=
⟨flip, λ _ _, rfl, λ _ _, rfl⟩
variables {R M N P}

@[simp] theorem lflip_apply (m : M) (n : N) : lflip R M N P f n m = f m n := rfl

theorem map_zero₂ (y) : f 0 y = 0 := (flip f y).map_zero

theorem map_neg₂ (x y) : f (-x) y = -f x y := (flip f y).map_neg _

theorem map_add₂ (x₁ x₂ y) : f (x₁ + x₂) y = f x₁ y + f x₂ y := (flip f y).map_add _ _

theorem map_smul₂ (r x y) : f (r • x) y = r • f x y := (flip f y).map_smul _ _

variables (P)
def lcomp (f : M →ₗ N) : (N →ₗ P) →ₗ M →ₗ P :=
flip $ (flip id).comp f
variables {P}

@[simp] theorem lcomp_apply (f : M →ₗ N) (g : N →ₗ P) (x : M) :
  lcomp P f g x = g (f x) := rfl

variables (M N P)
def llcomp : (N →ₗ P) →ₗ (M →ₗ N) →ₗ M →ₗ P :=
flip ⟨lcomp P,
  λ f f', ext₂ $ λ g x, g.map_add _ _,
  λ c f, ext₂ $ λ g x, g.map_smul _ _⟩
variables {M N P}

section
@[simp] theorem llcomp_apply (f : N →ₗ P) (g : M →ₗ N) (x : M) :
  llcomp M N P f g x = f (g x) := rfl
end

def compl₂ (g : Q →ₗ N) : M →ₗ Q →ₗ P := (lcomp _ g).comp f

@[simp] theorem compl₂_apply (g : Q →ₗ N) (m : M) (q : Q) :
  f.compl₂ g m q = f m (g q) := rfl

def compr₂ (g : P →ₗ Q) : M →ₗ N →ₗ Q :=
linear_map.comp (llcomp N P Q g) f

@[simp] theorem compr₂_apply (g : P →ₗ Q) (m : M) (n : N) :
  f.compr₂ g m n = g (f m n) := rfl

variables (R M)
def lsmul : R →ₗ M →ₗ M :=
mk₂ (•) add_smul (λ _ _ _, eq.symm $ smul_smul _ _ _) smul_add
(λ r s m, by simp only [smul_smul, smul_eq_mul, mul_comm])
variables {R M}

@[simp] theorem lsmul_apply (r : R) (m : M) : lsmul R M r m = r • m := rfl

end linear_map

variables (M N)

namespace tensor_product

def relators : set (free_abelian_group (M × N)) :=
add_group.closure { x : free_abelian_group (M × N) |
  (∃ (m₁ m₂ : M) (n : N), x = (m₁, n) + (m₂, n) - (m₁ + m₂, n)) ∨
  (∃ (m : M) (n₁ n₂ : N), x = (m, n₁) + (m, n₂) - (m, n₁ + n₂)) ∨
  (∃ (r : R) (m : M) (n : N), x = (r • m, n) - (m, r • n)) }

namespace relators

instance : normal_add_subgroup (relators M N) :=
by unfold relators; apply normal_add_subgroup_of_add_comm_group

end relators

end tensor_product

def tensor_product : Type* :=
quotient_add_group.quotient (tensor_product.relators M N)

local infix ` ⊗ `:100 := tensor_product

namespace tensor_product

section module

local attribute [instance] quotient_add_group.left_rel normal_add_subgroup.to_is_add_subgroup

instance : add_comm_group (M ⊗ N) := quotient_add_group.add_comm_group _

instance quotient.mk.is_add_group_hom :
  is_add_group_hom (quotient.mk : free_abelian_group (M × N) → M ⊗ N) :=
quotient_add_group.is_add_group_hom _

variables {M N}

def tmul (m : M) (n : N) : M ⊗ N := quotient_add_group.mk $ free_abelian_group.of (m, n)

infix ` ⊗ₜ `:100 := tmul

lemma add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) ⊗ₜ n = m₁ ⊗ₜ n + m₂ ⊗ₜ n :=
eq.symm $ sub_eq_zero.1 $ eq.symm $ quotient.sound $
  group.in_closure.basic $ or.inl $ ⟨m₁, m₂, n, rfl⟩

lemma tmul_add (m : M) (n₁ n₂ : N) : m ⊗ₜ (n₁ + n₂) = m ⊗ₜ n₁ + m ⊗ₜ n₂ :=
eq.symm $ sub_eq_zero.1 $ eq.symm $ quotient.sound $
  group.in_closure.basic $ or.inr $ or.inl $ ⟨m, n₁, n₂, rfl⟩

lemma smul_tmul (r : R) (m : M) (n : N) : (r • m) ⊗ₜ n = m ⊗ₜ (r • n) :=
sub_eq_zero.1 $ eq.symm $ quotient.sound $
  group.in_closure.basic $ or.inr $ or.inr $ ⟨r, m, n, rfl⟩

local attribute [instance] quotient_add_group.is_add_group_hom_quotient_lift

def smul.aux (r : R) : free_abelian_group (M × N) → M ⊗ N :=
free_abelian_group.lift (λ (y : M × N), (r • y.1) ⊗ₜ y.2)

instance (r : R) : is_add_group_hom (smul.aux r : _ → M ⊗ N) :=
by unfold smul.aux; apply_instance

instance : has_scalar R (M ⊗ N) :=
⟨λ r, quotient_add_group.lift _ (smul.aux r) $ λ x hx, begin
  refine (is_add_group_hom.mem_ker (smul.aux r : _ → M ⊗ N)).1
    (add_group.closure_subset _ hx),
  clear hx x, rintro x (⟨m₁, m₂, n, rfl⟩ | ⟨m, n₁, n₂, rfl⟩ | ⟨q, m, n, rfl⟩);
  simp only [smul.aux, is_add_group_hom.mem_ker, -sub_eq_add_neg,
    sub_self, add_tmul, tmul_add, smul_tmul,
    smul_add, smul_smul, mul_comm, free_abelian_group.lift.coe,
    free_abelian_group.lift.add, free_abelian_group.lift.sub]
end⟩

instance smul.is_add_group_hom (r : R) : is_add_group_hom ((•) r : M ⊗ N → M ⊗ N) :=
by unfold has_scalar.smul; apply_instance

protected theorem smul_add (r : R) (x y : M ⊗ N) :
  r • (x + y) = r • x + r • y :=
is_add_group_hom.add _ _ _

instance : module R (M ⊗ N) := module.of_core
{ smul := (•),
  smul_add := tensor_product.smul_add,
  add_smul := begin
      intros r s x,
      apply quotient_add_group.induction_on' x,
      intro z,
      symmetry,
      refine @free_abelian_group.lift.unique _ _ _ _ _ ⟨λ p q, _⟩ _ z,
      { simp [tensor_product.smul_add] },
      rintro ⟨m, n⟩,
      change (r • m) ⊗ₜ n + (s • m) ⊗ₜ n = ((r + s) • m) ⊗ₜ n,
      rw [add_smul, add_tmul]
    end,
  mul_smul := begin
      intros r s x,
      apply quotient_add_group.induction_on' x,
      intro z,
      symmetry,
      refine @free_abelian_group.lift.unique _ _ _ _ _
        ⟨λ p q, _⟩ _ z,
      { simp [tensor_product.smul_add] },
      rintro ⟨m, n⟩,
      change r • s • (m ⊗ₜ n) = ((r * s) • m) ⊗ₜ n,
      rw mul_smul, refl
    end,
  one_smul := λ x, quotient.induction_on x $ λ _,
    eq.symm $ free_abelian_group.lift.unique _ _ $ λ ⟨p, q⟩,
    by rw one_smul; refl }

@[simp] lemma tmul_smul (r : R) (x : M) (y : N) : x ⊗ₜ (r • y) = r • (x ⊗ₜ y) :=
(smul_tmul _ _ _).symm

variables (R M N)
def mk : M →ₗ N →ₗ M ⊗ N :=
linear_map.mk₂ (⊗ₜ) add_tmul (λ c m n, by rw [smul_tmul, tmul_smul]) tmul_add tmul_smul
variables {R M N}

@[simp] lemma mk_apply (m : M) (n : N) : mk R M N m n = m ⊗ₜ n := rfl

lemma zero_tmul (n : N) : (0 ⊗ₜ n : M ⊗ N) = 0 := (mk R M N).map_zero₂ _
lemma tmul_zero (m : M) : (m ⊗ₜ 0 : M ⊗ N) = 0 := (mk R M N _).map_zero
lemma neg_tmul (m : M) (n : N) : (-m) ⊗ₜ n = -(m ⊗ₜ n) := (mk R M N).map_neg₂ _ _
lemma tmul_neg (m : M) (n : N) : m ⊗ₜ (-n) = -(m ⊗ₜ n) := (mk R M N _).map_neg _

end module

local attribute [instance] quotient_add_group.left_rel normal_add_subgroup.to_is_add_subgroup

@[elab_as_eliminator]
protected theorem induction_on
  {C : M ⊗ N → Prop}
  (z : M ⊗ N)
  (C0 : C 0)
  (C1 : ∀ x y, C $ x ⊗ₜ y)
  (Cp : ∀ x y, C x → C y → C (x + y)) : C z :=
quotient.induction_on z $ λ x, free_abelian_group.induction_on x
  C0 (λ ⟨p, q⟩, C1 p q)
  (λ ⟨p, q⟩ _, show C (-(p ⊗ₜ q)), by rw ← neg_tmul; from C1 (-p) q)
  (λ _ _, Cp _ _)

section UMP

variables {M N P Q}
variables (f : M →ₗ N →ₗ P)

local attribute [instance] free_abelian_group.lift.is_add_group_hom

def lift_aux : M ⊗ N → P :=
quotient_add_group.lift _
  (free_abelian_group.lift $ λ z, f z.1 z.2) $ λ x hx,
begin
  refine (is_add_group_hom.mem_ker _).1 (add_group.closure_subset _ hx),
  clear hx x, rintro x (⟨m₁, m₂, n, rfl⟩ | ⟨m, n₁, n₂, rfl⟩ | ⟨q, m, n, rfl⟩);
    simp [is_add_group_hom.mem_ker, -sub_eq_add_neg,
      f.map_add, f.map_add₂, f.map_smul, f.map_smul₂, sub_self],
end
variable {f}

local attribute [instance] quotient_add_group.left_rel normal_add_subgroup.to_is_add_subgroup

@[simp] lemma lift_aux.add (x y) : lift_aux f (x + y) = lift_aux f x + lift_aux f y :=
quotient.induction_on₂ x y $ λ m n, free_abelian_group.lift.add _ _ _

@[simp] lemma lift_aux.smul (r x) : lift_aux f (r • x) = r • lift_aux f x :=
tensor_product.induction_on _ _ x (smul_zero _).symm
  (λ p q, by rw [← tmul_smul]; simp [lift_aux, tmul])
  (λ p q ih1 ih2, by simp [@smul_add _ _ _ _ _ _ p _,
    lift_aux.add, ih1, ih2, smul_add])

variable (f)
def lift : M ⊗ N →ₗ P :=
{ to_fun := lift_aux f,
  add := lift_aux.add,
  smul := lift_aux.smul }
variable {f}

@[simp] lemma lift.tmul (x y) : lift f (x ⊗ₜ y) = f x y :=
zero_add _

@[simp] lemma lift.tmul' (x y) : (lift f).1 (x ⊗ₜ y) = f x y :=
lift.tmul _ _

theorem lift.unique {g : linear_map (M ⊗ N) P} (H : ∀ x y, g (x ⊗ₜ y) = f x y) :
  g = lift f :=
linear_map.ext $ λ z, begin
  apply quotient_add_group.induction_on' z,
  intro z,
  refine @free_abelian_group.lift.unique _ _ _ _ _ ⟨λ p q, _⟩ _ z,
  { simp [g.2] },
  exact λ ⟨m, n⟩, H m n
end

theorem lift_mk : lift (mk R M N) = linear_map.id :=
eq.symm $ lift.unique $ λ x y, rfl

theorem lift_compr₂ (g : P →ₗ Q) : lift (f.compr₂ g) = g.comp (lift f) :=
eq.symm $ lift.unique $ λ x y, by simp

theorem lift_mk_compr₂ (f : M ⊗ N →ₗ P) : lift ((mk R M N).compr₂ f) = f :=
by rw [lift_compr₂, lift_mk, linear_map.comp_id]

theorem ext {g h : M ⊗ N →ₗ P}
  (H : ∀ x y, g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h :=
by rw ← lift_mk_compr₂ h; exact lift.unique H

theorem mk_compr₂_inj {g h : M ⊗ N →ₗ P}
  (H : (mk R M N).compr₂ g = (mk R M N).compr₂ h) : g = h :=
by rw [← lift_mk_compr₂ g, H, lift_mk_compr₂]

example : M → N → (M → N → P) → P :=
λ m, flip $ λ f, f m

variables (M N P)
def uncurry : (M →ₗ N →ₗ P) →ₗ M ⊗ N →ₗ P :=
linear_map.flip $ lift $ (linear_map.lflip _ _ _ _).comp linear_map.id.flip
variables {M N P}

@[simp] theorem uncurry_apply (f : M →ₗ N →ₗ P) (m : M) (n : N) :
  uncurry M N P f (m ⊗ₜ n) = f m n :=
by rw [uncurry, linear_map.flip_apply, lift.tmul]; refl

variables (M N P)
def lift.equiv : (M →ₗ N →ₗ P) ≃ₗ (M ⊗ N →ₗ P) :=
{ inv_fun := λ f, (mk R M N).compr₂ f,
  left_inv := λ f, linear_map.ext₂ $ λ m n, lift.tmul _ _,
  right_inv := λ f, ext $ λ m n, lift.tmul _ _,
  .. uncurry M N P }

def lcurry : (M ⊗ N →ₗ P) →ₗ M →ₗ N →ₗ P :=
(lift.equiv M N P).symm
variables {M N P}

@[simp] theorem lcurry_apply (f : M ⊗ N →ₗ P) (m : M) (n : N) :
  lcurry M N P f m n = f (m ⊗ₜ n) := rfl

def curry (f : M ⊗ N →ₗ P) : M →ₗ N →ₗ P := lcurry M N P f

@[simp] theorem curry_apply (f : M ⊗ N →ₗ P) (m : M) (n : N) :
  curry f m n = f (m ⊗ₜ n) := rfl

end UMP

variables {M N}
protected def lid : R ⊗ M ≃ₗ M :=
linear_equiv.of_linear (lift $ linear_map.lsmul R M) (mk R R M 1)
  (linear_map.ext $ λ _, by simp)
  (ext $ λ r m, by simp; rw [← tmul_smul, ← smul_tmul, smul_eq_mul, mul_one])

protected def comm : M ⊗ N ≃ₗ N ⊗ M :=
linear_equiv.of_linear (lift (mk R N M).flip) (lift (mk R M N).flip)
  (ext $ λ m n, rfl)
  (ext $ λ m n, rfl)

open linear_map
protected def assoc : (M ⊗ N) ⊗ P ≃ₗ M ⊗ (N ⊗ P) :=
begin
  refine linear_equiv.of_linear
    (lift $ lift $ comp (lcurry _ _ _) $ mk _ _ _)
    (lift $ comp (uncurry _ _ _) $ curry $ mk _ _ _)
    (mk_compr₂_inj $ linear_map.ext $ λ m, ext $ λ n p, _)
    (mk_compr₂_inj $ flip_inj $ linear_map.ext $ λ p, ext $ λ m n, _);
  repeat { rw lift.tmul <|> rw compr₂_apply <|> rw comp_apply <|>
    rw mk_apply <|> rw flip_apply <|> rw lcurry_apply <|>
    rw uncurry_apply <|> rw curry_apply <|> rw id_apply }
end

def map (f : M →ₗ P) (g : N →ₗ Q) : M ⊗ N →ₗ P ⊗ Q :=
lift $ comp (compl₂ (mk _ _ _) g) f

@[simp] theorem map_tmul (f : M →ₗ P) (g : N →ₗ Q) (m : M) (n : N) :
  map f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
rfl

def congr (f : M ≃ₗ P) (g : N ≃ₗ Q) : M ⊗ N ≃ₗ P ⊗ Q :=
linear_equiv.of_linear (map f g) (map f.symm g.symm)
  (ext $ λ m n, by simp; simp only [linear_equiv.apply_symm_apply])
  (ext $ λ m n, by simp; simp only [linear_equiv.symm_apply_apply])

end tensor_product
