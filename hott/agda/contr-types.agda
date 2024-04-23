{-# OPTIONS --without-K --no-import-sorts --rewriting --allow-unsolved-metas #-}
module Tutorial202404Trey where

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

module _ {A : Type} {B : Type} where
  path-to-equiv : A ≡ B → A ≃ B
  f (path-to-equiv refl) a = a
  g (path-to-equiv refl) b = b
  η (path-to-equiv refl) x = refl
  h (path-to-equiv refl) a = a
  ϵ (path-to-equiv refl) y = refl
