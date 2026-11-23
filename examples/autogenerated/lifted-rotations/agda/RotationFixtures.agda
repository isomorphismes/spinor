{-# OPTIONS --safe --without-K #-}
module RotationFixtures where

open import Agda.Builtin.Equality using (_≡_; refl)
open import LiftedRotations

start : Lift
start = signed plus one

z-half-turn : Lift
z-half-turn = signed plus k

z-full-turn : Lift
z-full-turn = multiply z-half-turn z-half-turn

z-three-half-turns : Lift
z-three-half-turns = multiply z-half-turn z-full-turn

z-two-full-turns : Lift
z-two-full-turns = multiply z-half-turn z-three-half-turns

start-orientation : project start ≡ identity
start-orientation = refl

half-turn-orientation : project z-half-turn ≡ half-z
half-turn-orientation = refl

full-turn-lift : z-full-turn ≡ signed minus one
full-turn-lift = refl

full-turn-orientation : project z-full-turn ≡ project start
full-turn-orientation = refl

full-turn-changes-lift : z-full-turn ≡ start → Empty
full-turn-changes-lift = antipodes-differ start

three-half-turns-lift : z-three-half-turns ≡ signed minus k
three-half-turns-lift = refl

three-half-turns-orientation : project z-three-half-turns ≡ half-z
three-half-turns-orientation = refl

two-full-turns-restore-lift : z-two-full-turns ≡ start
two-full-turns-restore-lift = refl

two-full-turns-orientation : project z-two-full-turns ≡ identity
two-full-turns-orientation = refl

i-times-j : Lift
i-times-j = multiply (signed plus i) (signed plus j)

j-times-i : Lift
j-times-i = multiply (signed plus j) (signed plus i)

i-times-j-lift : i-times-j ≡ signed plus k
i-times-j-lift = refl

j-times-i-lift : j-times-i ≡ signed minus k
j-times-i-lift = refl

i-times-j-orientation : project i-times-j ≡ half-z
i-times-j-orientation = refl

j-times-i-orientation : project j-times-i ≡ half-z
j-times-i-orientation = refl

ordered-products-differ : j-times-i ≡ i-times-j → Empty
ordered-products-differ = antipodes-differ i-times-j

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl proof = proof

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

orientation-cannot-select-every-lift :
  (choose : Orientation → Lift) → ((lift : Lift) → choose (project lift) ≡ lift) → Empty
orientation-cannot-select-every-lift choose round-trip =
  full-turn-changes-lift (trans (sym (round-trip z-full-turn)) (round-trip start))
