
import data.equiv

universes u v w

class canonical_equiv (α : Sort*) (β : Sort*) extends equiv α β.

class transportable (f : Type u → Type u) :=
(on_equiv : Π {α β : Type u} (e : equiv α β), equiv (f α) (f β))
(on_refl  : Π (α : Type u), on_equiv (equiv.refl α) = equiv.refl (f α))
(on_trans : Π {α β γ : Type u} (d : equiv α β) (e : equiv β γ), on_equiv (equiv.trans d e) = equiv.trans (on_equiv d) (on_equiv e))

-- Finally a command like: `initialize_transport group` would create the next two declarations automagically:

#print group

open transportable

#print transportable


definition equiv_mul {α β : Type u} : equiv α β → equiv (has_mul α) (has_mul β) := λ E,
{ to_fun :=  λ αmul,⟨λ b1 b2, E.to_fun (@has_mul.mul α αmul (E.inv_fun b1) (E.inv_fun b2))⟩,
  inv_fun := λ βmul,⟨λ a1 a2, E.inv_fun (@has_mul.mul β βmul (E.to_fun a1) (E.to_fun a2))⟩, -- didn't I just write that?
                                                                      -- should we introduce E-dual?
  left_inv := λ f, begin
    cases f, simp, -- aargh why do I struggle
    congr,
    -- suffices :  (λ (a1 a2 : α), E.inv_fun (E.to_fun (f _ _))) = (λ a1 a2, f a1 a2),
    --   by rw this,
    funext,
    simp [E.left_inv _,E.right_inv _], -- got there in the end
  end,
  right_inv := -- I can't even do this in term mode so I just copy out the entire tactic mode proof again.
 λ g, begin
    cases g, simp, -- aargh why do I struggle
    suffices :  (λ (b1 b2 : β), E.to_fun (E.inv_fun (g _ _))) = (λ b1 b2, g b1 b2),
      by rw this,
    funext,
    simp [E.left_inv _,E.right_inv _], -- got there in the end
  end, -- didn't I just write that?
}



namespace group

variables {α β : Type u}
variables (eq : equiv α β)

@[simp] def tr₀ : α → β := eq
@[simp] def tr₁ (f : α → α) : β → β := λ x : β, eq (f $ eq.symm x)
@[simp] def tr₂ (f : α → α → α) : β → β → β := λ (x y : β), eq $ f (eq.symm x) (eq.symm y)
-- def etr₀ : β → α := eq.inv_fun
-- def etr₁ (f : β → β) (x : α) : α := eq.inv_fun (f $ eq.to_fun x)
-- def etr₂ (f : β → β → β) (x y : α) : α := eq.inv_fun $ f (eq.to_fun x) (eq.to_fun y)

-- @[simp]
-- lemma inv_fun_tr₀ (f : α) :
--   eq.inv_fun (tr₀ eq f) = f :=
-- by simp [tr₀,equiv.left_inv eq _]

-- @[simp]
-- lemma inv_fun_tr₁ (f : α → α) (x : β) :
--   eq.inv_fun (tr₁ eq f x) = f (eq.inv_fun x) :=
-- by simp [tr₁,equiv.left_inv eq _]

-- @[simp]
-- lemma inv_fun_tr₂ (f : α → α → α) (x y : β) :
--   eq.inv_fun (tr₂ eq f x y) = f (eq.inv_fun x) (eq.inv_fun y) :=
-- by simp [tr₂,equiv.left_inv eq _]

local attribute [simp] equiv.left_inv equiv.right_inv

-- @[simp]
-- lemma symm_inv_fun :
--   eq.symm.inv_fun = eq.to_fun :=
-- by cases eq ; refl

-- @[simp]
-- lemma symm_to_fun :
--   eq.symm.to_fun = eq.inv_fun :=
-- by cases eq ; refl

-- @[simp]
-- lemma inv_fun_etr₀ (f : β) :
--   eq.to_fun (etr₀ eq f) = f :=
-- by simp [etr₀,equiv.right_inv eq _]

-- @[simp]
-- lemma inv_fun_etr₁ (f : β → β) (x : α) :
--   eq.to_fun (etr₁ eq f x) = f (eq.to_fun x) :=
-- by simp [etr₁,equiv.left_inv eq _]

-- @[simp]
-- lemma inv_fun_etr₂ (f : α → α → α) (x y : β) :
--   eq.inv_fun (etr₂ eq f x y) = f (eq.inv_fun x) (eq.inv_fun y) :=
-- by simp [tr₂,equiv.left_inv eq _]

lemma inj {x y : β}
  (h : eq.symm x = eq.symm y)
: x = y := sorry

@[simp]
def on_equiv.to_fun [group α] : group β :=
{ one := tr₀ eq (one α)
, mul := tr₂ eq mul
, inv := tr₁ eq inv
, mul_left_inv := by { intros, apply inj eq, simp, apply mul_left_inv }
, one_mul := by { intros, apply inj eq, simp, apply one_mul }
, mul_one := by { intros, apply inj eq, simp [has_mul.mul], apply mul_one }
, mul_assoc := by { intros, apply inj eq, simp, apply mul_assoc }  }

@[simp]
def on_equiv.inv_fun [group β] : group α :=
{ one := tr₀ eq.symm (one _)
, mul := tr₂ eq.symm mul
, inv := tr₁ eq.symm inv
, mul_left_inv := by { intros, apply inj eq.symm, simp, apply mul_left_inv }
, one_mul := by { intros, apply inj eq.symm, simp, apply one_mul }
, mul_one := by { intros, apply inj eq.symm, simp [has_mul.mul], apply mul_one }
, mul_assoc := by { intros, apply inj eq.symm, simp, apply mul_assoc }  }

def on_equiv : group α ≃ group β :=
{ to_fun := @on_equiv.to_fun _ _ eq,
  inv_fun := @on_equiv.inv_fun _ _ eq,
  right_inv := by { intro x, cases x, simp, -- aargh why do I struggle
    congr ;
    -- suffices :  (λ (a1 a2 : α), E.inv_fun (E.to_fun (f _ _))) = (λ a1 a2, f a1 a2),
    --   by rw this,
    funext ;
    dsimp [mul,one,inv] ;
    simp!, },
  left_inv := by { intro x, cases x, simp, -- aargh why do I struggle
    congr ;
    -- suffices :  (λ (a1 a2 : α), E.inv_fun (E.to_fun (f _ _))) = (λ a1 a2, f a1 a2),
    --   by rw this,
    funext ;
    dsimp [mul,one,inv] ;
    simp!, } }

def transportable : transportable group :=
begin
  refine { on_equiv := @on_equiv, .. }
  ; intros ; simp [on_equiv,equiv.refl,equiv.trans]
  ; split ; funext x ; cases x ; refl,
end

end group

#check derive_attr
instance group.transport {α β : Type u} [R : group α] [e : canonical_equiv α β] : group β :=
(@transportable.on_equiv group group.transportable _ _ e.to_equiv).to_fun R


-- class transportable (f : Type u → Type v) :=
-- (on_equiv : Π {α β : Type u} (e : equiv α β), equiv (f α) (f β))
-- (on_refl  : Π (α : Type u), on_equiv (equiv.refl α) = equiv.refl (f α))
-- (on_trans : Π {α β γ : Type u} (d : equiv α β) (e : equiv β γ), on_equiv (equiv.trans d e) = equiv.trans (on_equiv d) (on_equiv e))

-- -- Our goal is an automagic proof of the following
-- theorem group.transportable : transportable group := sorry

-- These we might need to define and prove by hand
def Const : Type u → Type v := λ α, punit
def Fun : Type u → Type v → Type (max u v) := λ α β, α → β
def Prod : Type u → Type v → Type (max u v) := λ α β, α × β
def Swap : Type u → Type v → Type (max u v) := λ α β, β × α

lemma Const.transportable (α : Type u) : (transportable Const) := sorry
lemma Fun.transportable (α : Type u) : (transportable (Fun α)) := sorry
lemma Prod.transportable (α : Type u) : (transportable (Prod α)) := sorry
lemma Swap.transportable (α : Type u) : (transportable (Swap α)) := sorry


-- And then we can define
def Hom1 (α : Type u) : Type v → Type (max u v) := λ β, α → β
def Hom2 (β : Type v) : Type u → Type (max u v) := λ α, α → β
def Aut : Type u → Type u := λ α, α → α

-- And hopefully automagically derive
lemma Hom1.transportable (α : Type u) : (transportable (Hom1 α)) := sorry
lemma Hom2.transportable (β : Type v) : (transportable (Hom1 β)) := sorry
lemma Aut.transportable (α : Type u) : (transportable Aut) := sorry

-- If we have all these in place...
-- A bit of magic might actually be able to derive `group.transportable` on line 11.
-- After all, a group just is a type plus some functions... and we can now transport functions.
