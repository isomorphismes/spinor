{-# OPTIONS --safe --without-K #-}
module LiftedRotations where

open import Agda.Builtin.Equality using (_≡_; refl)

data Empty : Set where

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

data Sign : Set where
  plus minus : Sign

flip : Sign → Sign
flip plus = minus
flip minus = plus

_×ₛ_ : Sign → Sign → Sign
plus ×ₛ right = right
minus ×ₛ right = flip right

data Basis : Set where
  one i j k : Basis

record Lift : Set where
  constructor signed
  field
    coefficient : Sign
    basis : Basis

antipode : Lift → Lift
antipode (signed sign axis) = signed (flip sign) axis

-- Rows are left factors in Hamilton's convention.
basis-product : Basis → Basis → Lift
basis-product one right = signed plus right
basis-product i one = signed plus i
basis-product i i = signed minus one
basis-product i j = signed plus k
basis-product i k = signed minus j
basis-product j one = signed plus j
basis-product j i = signed minus k
basis-product j j = signed minus one
basis-product j k = signed plus i
basis-product k one = signed plus k
basis-product k i = signed plus j
basis-product k j = signed minus i
basis-product k k = signed minus one

scale : Sign → Lift → Lift
scale by (signed sign axis) = signed (by ×ₛ sign) axis

multiply : Lift → Lift → Lift
multiply (signed left-sign left-basis) (signed right-sign right-basis) =
  scale (left-sign ×ₛ right-sign) (basis-product left-basis right-basis)

inverse : Lift → Lift
inverse (signed sign one) = signed sign one
inverse (signed sign i) = signed (flip sign) i
inverse (signed sign j) = signed (flip sign) j
inverse (signed sign k) = signed (flip sign) k

data SpatialAxis : Set where
  x-axis y-axis z-axis : SpatialAxis

pure : SpatialAxis → Basis
pure x-axis = i
pure y-axis = j
pure z-axis = k

conjugate-axis : Lift → SpatialAxis → Lift
conjugate-axis lift axis = multiply (multiply lift (signed plus (pure axis))) (inverse lift)

-- These four diagonal matrices have determinant +1. The names distinguish
-- the geometric rotations from the lifts used to represent them.
data Orientation : Set where
  identity half-x half-y half-z : Orientation

axis-orientation : Basis → Orientation
axis-orientation one = identity
axis-orientation i = half-x
axis-orientation j = half-y
axis-orientation k = half-z

project : Lift → Orientation
project (signed sign axis) = axis-orientation axis

axis-sign : Orientation → SpatialAxis → Sign
axis-sign identity axis = plus
axis-sign half-x x-axis = plus
axis-sign half-x y-axis = minus
axis-sign half-x z-axis = minus
axis-sign half-y x-axis = minus
axis-sign half-y y-axis = plus
axis-sign half-y z-axis = minus
axis-sign half-z x-axis = minus
axis-sign half-z y-axis = minus
axis-sign half-z z-axis = plus

conjugation-is-diagonal : (lift : Lift) (axis : SpatialAxis) →
  conjugate-axis lift axis ≡ signed (axis-sign (project lift) axis) (pure axis)
conjugation-is-diagonal (signed plus one) x-axis = refl
conjugation-is-diagonal (signed plus one) y-axis = refl
conjugation-is-diagonal (signed plus one) z-axis = refl
conjugation-is-diagonal (signed minus one) x-axis = refl
conjugation-is-diagonal (signed minus one) y-axis = refl
conjugation-is-diagonal (signed minus one) z-axis = refl
conjugation-is-diagonal (signed plus i) x-axis = refl
conjugation-is-diagonal (signed plus i) y-axis = refl
conjugation-is-diagonal (signed plus i) z-axis = refl
conjugation-is-diagonal (signed minus i) x-axis = refl
conjugation-is-diagonal (signed minus i) y-axis = refl
conjugation-is-diagonal (signed minus i) z-axis = refl
conjugation-is-diagonal (signed plus j) x-axis = refl
conjugation-is-diagonal (signed plus j) y-axis = refl
conjugation-is-diagonal (signed plus j) z-axis = refl
conjugation-is-diagonal (signed minus j) x-axis = refl
conjugation-is-diagonal (signed minus j) y-axis = refl
conjugation-is-diagonal (signed minus j) z-axis = refl
conjugation-is-diagonal (signed plus k) x-axis = refl
conjugation-is-diagonal (signed plus k) y-axis = refl
conjugation-is-diagonal (signed plus k) z-axis = refl
conjugation-is-diagonal (signed minus k) x-axis = refl
conjugation-is-diagonal (signed minus k) y-axis = refl
conjugation-is-diagonal (signed minus k) z-axis = refl

-- Composition measured on all three spatial axes is ordinary matrix
-- composition for the diagonal matrices. The components are checked together.
record Diagonal : Set where
  constructor signs
  field
    x y z : Sign

diagonal : Orientation → Diagonal
diagonal rotation = signs (axis-sign rotation x-axis)
                          (axis-sign rotation y-axis)
                          (axis-sign rotation z-axis)

determinant : Diagonal → Sign
determinant (signs sx sy sz) = sx ×ₛ (sy ×ₛ sz)

positive-determinant : (rotation : Orientation) → determinant (diagonal rotation) ≡ plus
positive-determinant identity = refl
positive-determinant half-x = refl
positive-determinant half-y = refl
positive-determinant half-z = refl

compose : Diagonal → Diagonal → Diagonal
compose (signs lx ly lz) (signs rx ry rz) = signs (lx ×ₛ rx) (ly ×ₛ ry) (lz ×ₛ rz)

projection-preserves-product : (left right : Lift) →
  diagonal (project (multiply left right)) ≡ compose (diagonal (project left)) (diagonal (project right))
projection-preserves-product (signed s one) (signed t one) = refl
projection-preserves-product (signed s one) (signed t i) = refl
projection-preserves-product (signed s one) (signed t j) = refl
projection-preserves-product (signed s one) (signed t k) = refl
projection-preserves-product (signed s i) (signed t one) = refl
projection-preserves-product (signed s i) (signed t i) = refl
projection-preserves-product (signed s i) (signed t j) = refl
projection-preserves-product (signed s i) (signed t k) = refl
projection-preserves-product (signed s j) (signed t one) = refl
projection-preserves-product (signed s j) (signed t i) = refl
projection-preserves-product (signed s j) (signed t j) = refl
projection-preserves-product (signed s j) (signed t k) = refl
projection-preserves-product (signed s k) (signed t one) = refl
projection-preserves-product (signed s k) (signed t i) = refl
projection-preserves-product (signed s k) (signed t j) = refl
projection-preserves-product (signed s k) (signed t k) = refl

antipodes-project-equally : (q : Lift) → project (antipode q) ≡ project q
antipodes-project-equally (signed sign axis) = refl

opposite-signs-differ : (sign : Sign) → flip sign ≡ sign → Empty
opposite-signs-differ plus ()
opposite-signs-differ minus ()

antipodes-differ : (q : Lift) → antipode q ≡ q → Empty
antipodes-differ (signed sign axis) equality = opposite-signs-differ sign (cong Lift.coefficient equality)

positive-representative : Orientation → Lift
positive-representative identity = signed plus one
positive-representative half-x = signed plus i
positive-representative half-y = signed plus j
positive-representative half-z = signed plus k

project-representative : (rotation : Orientation) → project (positive-representative rotation) ≡ rotation
project-representative identity = refl
project-representative half-x = refl
project-representative half-y = refl
project-representative half-z = refl

data SameFiber : Lift → Lift → Set where
  same : (q : Lift) → SameFiber q q
  opposite : (q : Lift) → SameFiber q (antipode q)

classify-signs : (left right : Sign) (axis : Basis) → SameFiber (signed left axis) (signed right axis)
classify-signs plus plus axis = same (signed plus axis)
classify-signs plus minus axis = opposite (signed plus axis)
classify-signs minus plus axis = opposite (signed minus axis)
classify-signs minus minus axis = same (signed minus axis)

axis-injective : (first second : Basis) → axis-orientation first ≡ axis-orientation second → first ≡ second
axis-injective one one _ = refl
axis-injective one i ()
axis-injective one j ()
axis-injective one k ()
axis-injective i one ()
axis-injective i i _ = refl
axis-injective i j ()
axis-injective i k ()
axis-injective j one ()
axis-injective j i ()
axis-injective j j _ = refl
axis-injective j k ()
axis-injective k one ()
axis-injective k i ()
axis-injective k j ()
axis-injective k k _ = refl

classify-lift-bases : (s t : Sign) (first second : Basis) → first ≡ second →
  SameFiber (signed s first) (signed t second)
classify-lift-bases s t axis .axis refl = classify-signs s t axis

projection-fiber : (left right : Lift) → project left ≡ project right → SameFiber left right
projection-fiber (signed s first) (signed t second) equality =
  classify-lift-bases s t first second (axis-injective first second equality)
