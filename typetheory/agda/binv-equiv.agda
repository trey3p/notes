{-# OPTIONS --without-K --no-import-sorts --rewriting --allow-unsolved-metas #-}
module binv-equiv where
-- Proofs of equivalence with bi-invertible equivalences
--
open import Agda.Primitive renaming (Set to Type) public

infixr 4 _≡_


data _≡_ {l : Level} {X : Type l} (x1 : X) : (x2 : X) -> Type l where
  refl : x1 ≡ x1

{-# BUILTIN REWRITE _≡_ #-}

ap : {X Y : Type} -> (f : X -> Y) -> {x1 x2 : X} -> (p : x1 ≡ x2) -> f x1 ≡ f x2
ap f refl = refl

tpt : {X : Type} -> (P : X -> Type) -> {x1 x2 : X} -> (p : x1 ≡ x2) -> P x1 -> P x2
tpt P refl p = p

apd : {X : Type} -> (P : X -> Type) -> (f : (x : X) -> P x) -> {x1 x2 : X} -> (p : x1 ≡ x2) ->
      tpt P p (f x1) ≡ f x2
apd P f refl = refl

infixr 8 _•_
_•_ : {X : Type} -> {x1 x2 x3 : X} -> (p : x1 ≡ x2) -> (q : x2 ≡ x3) -> x1 ≡ x3
p • refl = p

infix 10 !
! : {X : Type} -> {x1 x2 : X} -> (p : x1 ≡ x2) -> x2 ≡ x1
! refl = refl

infixr 5 _⊎_
data _⊎_ (X : Type) (Y : Type) : Type where
  inl : X -> X ⊎ Y
  inr : Y -> X ⊎ Y

infix 4 _≃_
record _≃_ (X : Type) (Y : Type) : Type where
  constructor biinv
  field
    f : X -> Y
    g : Y -> X
    η : (x : X) → g (f x) ≡ x
    h : Y -> X
    ϵ : (y : Y) → f (h y) ≡ y
open _≃_ public

module _ {X : Type} {Y : Type} (e : X ≃ Y) where
  -- f is a left inverse of g
  ϵ' : (y : Y) → f e (g e y) ≡ y
  ϵ' y = ! (ap (λ y → f e (g e y)) (ϵ e y)) • ap (f e) (η e (h e y)) • ϵ e y
  -- Define η'
  -- h is a left inverse of f
  η' : (x : X) →  h e (f e x) ≡ x
  η' x =  !(η e (h e (f e x))) • ap (g e) (ϵ e (f e x)) • η e x
  --  ap (h e) (ϵ' (f e x))
  τ' : (x : X) -> ap (f e) (η e x) ≡ ϵ' (f e x)
  τ' x = {!!}


data Unit : Type where
  ⋆ : Unit

-- Proof of A ≃ (Unit → A)

postulate
  ∀-extensionality : ∀ {A : Type} {B : A → Type} {f g : ∀(x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

module ≃-Unit-fun {A : Type} where
    to : A → (Unit → A)
    to a _ = a

    from1 : (Unit → A) → A
    from1 f = f ⋆

    from-to : (a : A) → from1 (to a) ≡ a
    from-to a = refl

    from2 : (Unit → A) → A
    from2 f = f ⋆

    to-from : (f : Unit → A) → to (from2 f) ≡ f
    to-from f = ∀-extensionality λ{ ⋆ → refl}

    Unit→A≃A : A ≃ (Unit → A)
    Unit→A≃A = biinv to from1 from-to from2 to-from

postulate
  Z : Type
  zero : Z
  e : Z ≃ Z

module _ {P : Z -> Type} (z* : P zero)
         (e* : (m : Z) → P m ≃ P (f e m)) where

  postulate
    indZ : (m : Z) -> P m
    indZ-zero : indZ zero ≡ z*
  {-# REWRITE indZ-zero #-}

  postulate
    indZ-e : (m : Z) -> indZ (f e m) ≡ f (e* m) (indZ m)


module Recursion where
  module _ {Y : Type} (z* : Y) (e* : Y ≃ Y) where
    recZ : Z -> Y
    recZ = indZ {P = λ _ -> Y} z* (λ _ -> e*)

    recZ-zero : recZ zero ≡ z*
    recZ-zero = refl

    recZ-e : (m : Z) -> recZ (f e m) ≡ f e* (recZ m)
    recZ-e m = indZ-e z* (λ m → e*) m

    recZ-ϵ : (m : Z) -> recZ m ≡ f e* (recZ (g e m))
    recZ-ϵ m = ! (ap (λ m → recZ m) (ϵ' e m)) • recZ-e (g e m)

    recZ-!e : (m : Z) -> recZ (g e m) ≡ g e* (recZ m)
    recZ-!e m = !(η e* (recZ (g e m))) • ap (g e*) (!(recZ-e (g e m))) • ap (g e*) (ap recZ (ϵ' e m))

    recZ-η : (m : Z) -> recZ m ≡ g e* (recZ (f e m))
    recZ-η m = !(ap (λ m → recZ m) (η e m)) • recZ-!e (f e m)

-- Proof of Z ≃ Int

data Nat : Type where
  z : Nat
  suc : Nat -> Nat

ind-ℕ : {P : Nat → Type} → P z → ((n : Nat) → P n → P(suc n)) → ((n : Nat) → P n)
ind-ℕ p0 pS z = p0
ind-ℕ p0 pS (suc n) = pS n (ind-ℕ p0 pS n)

recℕ : (X : Type) -> (z* : X) -> (suc* : X → X) → (Nat → X)
recℕ X z* suc* x = ind-ℕ {P = λ _ → X} z* (λ n → suc*) x

Int : Type
Int = Nat ⊎ (Unit ⊎ Nat)

in-pos : Nat → Int
in-pos x = inr (inr x)

in-neg : Nat → Int
in-neg x = inl x


1-ℤ : Int
1-ℤ = in-pos(z)

0-ℤ : Int
0-ℤ = inr(inl ⋆)

-1-ℤ : Int
-1-ℤ = in-neg(z)

pred-ℤ : Int → Int
pred-ℤ (inl x) = (inl (suc x))
pred-ℤ (inr (inl ⋆)) = inl z
pred-ℤ (inr (inr z)) = 0-ℤ
pred-ℤ (inr (inr (suc x))) = inr (inr x)

suc-ℤ : Int → Int
suc-ℤ (inl z) = 0-ℤ
suc-ℤ (inl (suc x)) = inl x
suc-ℤ (inr (inl ⋆)) = 1-ℤ
suc-ℤ (inr (inr x)) = inr (inr (suc x))

postulate
  indInt : {P : Int → Type} → (z* : P 0-ℤ) → (e* : (m : Int) → P m ≃ P (suc-ℤ m)) → ((m : Int) → P m)
  recInt : (X : Type) → (b : X) → (f : X → X) → (Int → X)
  recInt-zero : recInt Z zero (λ x → x) 0-ℤ ≡ zero

add-ℤ : Int → (Int → Int)
add-ℤ (inl z) y = pred-ℤ y
add-ℤ (inl (suc x)) y = add-ℤ (inl x) (pred-ℤ y)
add-ℤ (inr (inl ⋆)) y = y
add-ℤ (inr (inr z)) y = suc-ℤ y
add-ℤ (inr (inr (suc x))) y = add-ℤ (inr (inr x)) (suc-ℤ y)

neg-ℤ : Int → Int
neg-ℤ (inl z) = 1-ℤ
neg-ℤ (inl (suc x)) = inr (inr (suc x))
neg-ℤ (inr (inl ⋆)) = 0-ℤ
neg-ℤ (inr (inr x)) = inl x


mul-ℤ : Int → (Int → Int)
mul-ℤ (inl z) y = neg-ℤ y
mul-ℤ (inl (suc x)) y = add-ℤ (mul-ℤ (inl x)  y) (neg-ℤ y)
mul-ℤ (inr (inl ⋆)) y = 0-ℤ
mul-ℤ (inr (inr z)) y = y
mul-ℤ (inr (inr (suc x))) y = add-ℤ (mul-ℤ (inr (inr x)) y) (y)


module _ where
  help1 = Recursion.recZ z* e*
    where
    z* : Int
    z* = 0-ℤ
    e* : Int ≃ Int
    f e* x = x
    g e* x = x
    η e* x = refl
    h e* x = x
    ϵ e* y = refl

  help2 = recInt Z b s
    where
    b : Z
    b = zero
    s : Z → Z
    s x = x

  id-equiv : Int ≃ Int
  id-equiv = record { f = λ x → x ; g = λ x → x ; η = λ _ → refl ; h = λ x → x ; ϵ = λ _ → refl }

  help3 = indZ z* e*
    where
    z* : help2 (help1 zero) ≡ zero
    z* = ap help2 (ap help1 refl) • ap (recInt Z zero (λ x → x)) (Recursion.recZ-zero 0-ℤ (id-equiv)) • recInt-zero

    e* : (x : Z) → ((help2 (help1 x) ≡ x) ≃ ((help2 (help1 (f e x))) ≡ (f e x)))
    -- (e* : (m : Z) → P m ≃ P (f e m))
    f (e* x) = {!!}
    g (e* x) = {!!}
    η (e* x) = {!!}
    h (e* x) = {!!}
    ϵ (e* x) = {!!}

  equiv : Z ≃ Int
  f equiv x = help1 x
  g equiv x = help2 x
  η equiv x = {!!}
  h equiv = {!!}
  ϵ equiv = {!!}
-- A ≡ B implies A ≃ B

module _ {A : Type} {B : Type} where
  path-to-equiv : A ≡ B → A ≃ B
  f (path-to-equiv refl) a = a
  g (path-to-equiv refl) b = b
  η (path-to-equiv refl) x = refl
  h (path-to-equiv refl) a = a
  ϵ (path-to-equiv refl) y = refl
