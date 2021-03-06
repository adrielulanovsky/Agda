
module EjemplosFSets where

open import Categories.Iso
open import Categories.Sets
open import Categories.Products
open import Categories.Coproducts
open import Categories.Terminal
open import Categories.Initial
open import Functors
open import Functors.Constant
open import Library hiding (_×_ ; _+_)

open Products (SetsHasProducts {lzero})
open Coproducts (SetsHasCoproducts {lzero}) 
open Terminal OneSet
open Initial ZeroSet

open import Functors.Product (SetsHasProducts {lzero})
open import Functors.Coproduct (SetsHasCoproducts {lzero})


--------------------------------------------------
{- Definir el siguiente funtor sobre Sets
 *usando suma y producto de functores*
 La idea es reusarlo que ya está definido.
 *No* definir functores usando el constructor de funtores.
  -}

-- Nat X = 1 + X
Nat : Fun Sets Sets
Nat = (K ⊤) +F IdF

module Nat where

  open Fun Nat
  open import Functors.Algebra Nat
  open F-homomorphism
  open F-algebra

  FNat-Nat : (OMap ℕ) -> ℕ
  FNat-Nat = [ (λ x → 0) , suc ]

--demuestro que Nat es un álgebra:
  NatAlgebra : F-algebra
  NatAlgebra = falgebra ℕ FNat-Nat

  -- definir constructores
  0N : μF
  0N = (α ∘ inl) ⊤.tt
  sucN : μF → μF
  sucN x = (α ∘ inr) x

{- Probar que el portador de la semántica de algebra inicial
  de OnePlus es igual a ℕ

Nota: quiero probar que μF es isomorfo a ℕ
-}
  Natμ : ℕ -> μF
  Natμ zero = 0N
  Natμ (suc x) = sucN (Natμ x)
 
  lemmaAlpha : α ≅ [ (λ x → 0N) , sucN ]
  lemmaAlpha = Coproducts.law3 SetsHasCoproducts refl refl

  lemmaIso1 : [ ((fold FNat-Nat) ∘ (λ x -> 0N)) , ((fold FNat-Nat) ∘ sucN) ] ≅ [ (λ x → 0) , suc ∘ (fold FNat-Nat) ]
  lemmaIso1 = proof
    [ (fold FNat-Nat) ∘ (λ x → 0N) , (fold FNat-Nat) ∘ sucN ]
    ≅⟨ sym (Coproducts.law3 SetsHasCoproducts {h = fold FNat-Nat ∘ [_,_] (λ x → 0N) sucN} refl refl) ⟩
    (fold FNat-Nat) ∘ [ (λ x → 0N) , sucN ]
    ≅⟨ cong (λ x -> (fold FNat-Nat) ∘ x) (sym lemmaAlpha) ⟩
    (fold FNat-Nat) ∘ α
    ≅⟨ homo-prop init-homo ⟩
    FNat-Nat ∘ (HMap (homo-base init-homo))
    ≅⟨ refl ⟩
    [ (λ x → 0) , suc ] ∘ (HMap (homo-base init-homo))
    ≅⟨ Coproducts.law3 SetsHasCoproducts
         {h = [_,_] (λ x → 0) suc ∘ HMap (homo-base init-homo)} refl refl ⟩
    [ (λ x → 0) , suc ∘ (fold FNat-Nat) ]
    ∎

  coproductCong1 : ∀{X Y Z}{a c : X -> Y}{b d : Z -> Y} -> [ a , b ] ≅ [ c , d ] -> a ≅ c
  coproductCong1 {a = a}{c}{b}{d} p = proof
   a
   ≅⟨ sym (Coproducts.law1 SetsHasCoproducts {f = a}{b}) ⟩
   [ a , b ] ∘ inl
   ≅⟨ cong (λ x -> x ∘ inl) p ⟩
   [ c , d ] ∘ inl
   ≅⟨ (Coproducts.law1 SetsHasCoproducts) {f = c}{d} ⟩
   c
   ∎

  coproductCong2 : ∀{X Y Z}{a c : X -> Y}{b d : Z -> Y} -> [ a , b ] ≅ [ c , d ] -> b ≅ d
  coproductCong2 {a = a}{c}{b}{d} p = proof
   b
   ≅⟨ sym (Coproducts.law2 SetsHasCoproducts {f = a}{b}) ⟩
   [ a , b ] ∘ inr
   ≅⟨ cong (λ x -> x ∘ inr) p ⟩
   [ c , d ] ∘ inr
   ≅⟨ (Coproducts.law2 SetsHasCoproducts) {f = c}{d} ⟩
   d
   ∎

  lemmaNat1 : (x : ℕ) -> ((fold FNat-Nat) ∘ Natμ) x ≅ x
  lemmaNat1 zero = proof
    (fold FNat-Nat) 0N
    ≅⟨ cong-app (coproductCong1 lemmaIso1) ⊤.tt ⟩
    0
    ∎
  lemmaNat1 (suc x) = proof
    ((fold FNat-Nat) ∘ sucN) (Natμ x)
    ≅⟨ cong-app (coproductCong2 lemmaIso1) (Natμ x) ⟩
    (suc ∘ (fold FNat-Nat)) (Natμ x)
    ≅⟨ cong (λ x -> suc x) (lemmaNat1 x) ⟩
    suc x
    ∎

  lemmaNatμHomo : (x : OMap ℕ) ->
                  (Natμ ∘ FNat-Nat) x ≅ (α ∘ HMap Natμ) x
  lemmaNatμHomo (Inl x) = refl
  lemmaNatμHomo (Inr x) = refl

  natμHomo : F-homomorphism NatAlgebra inF
  natμHomo = homo Natμ (ext lemmaNatμHomo)

  iso2Homomorphism : F-homomorphism inF inF
  iso2Homomorphism = homo (Natμ ∘ (fold FNat-Nat))
                          (proof
   Natμ ∘ fold FNat-Nat ∘ α
   ≅⟨ cong (λ x -> Natμ ∘ fold FNat-Nat ∘ x) lemmaAlpha ⟩
   Natμ ∘ fold FNat-Nat ∘ [ (λ x → 0N) , sucN ]
   ≅⟨ cong (λ x -> Natμ ∘ x) (Coproducts.law3 SetsHasCoproducts {h = fold FNat-Nat ∘ [_,_] (λ x → 0N) sucN} refl refl) ⟩
   Natμ ∘ [ fold FNat-Nat ∘ (λ x → 0N) , (fold FNat-Nat) ∘ sucN ]
   ≅⟨ cong (λ x -> Natμ ∘ x) lemmaIso1 ⟩
   Natμ ∘ [ (λ x → 0) , suc ∘ fold FNat-Nat ]
   ≅⟨ cong (λ x -> Natμ ∘ x) (sym (Coproducts.law3 SetsHasCoproducts {h = FNat-Nat ∘ (HMap (fold FNat-Nat))} refl refl)) ⟩
   (Natμ ∘ FNat-Nat) ∘ (HMap (fold FNat-Nat))
   ≅⟨ cong (λ x -> x ∘ (HMap (fold FNat-Nat))) (homo-prop natμHomo) ⟩
   α ∘ (HMap Natμ) ∘ HMap (fold FNat-Nat)
   ≅⟨ cong (λ x -> α ∘ x) (sym fcomp) ⟩
   α ∘ HMap (Natμ ∘ fold FNat-Nat)
   ∎)

  lemmaNat2 : Natμ ∘ (fold FNat-Nat) ≅ id
  lemmaNat2 = proof
                                 Natμ ∘ (fold FNat-Nat)
                                 ≅⟨ sym (cong homo-base (univ {f = iso2Homomorphism})) ⟩
                                 homo-base (init-homo {inF})
                                 ≅⟨ cong homo-base (univ {f = iden-homo}) ⟩
                                 homo-base (iden-homo {inF})
                                 ≅⟨ refl ⟩
                                 id
                                 ∎

  --intentar probar que [zero, suc] es un f-algebra inicial  

  lemaNat : Iso Sets (fold FNat-Nat)
  lemaNat = iso Natμ 
                (ext lemmaNat1) 
                lemmaNat2

--------------------------------------------------
{- Definir un functor cuya algebra inicial sea las listas.
-}

L : (A : Set) → Fun Sets Sets
L A = (K ⊤) +F ({!IdF!} ×F {!!})
module Listas (A : Set) where

  open Fun (L A)
  open import Functors.Algebra (L A)
  open F-homomorphism
  open F-algebra

{-
   Definir constructores, y probar que
   efectivamente son listas (como hicimos con los naturales)
-}


  


{-
  Definir la función length para listas
-}

  length : μF → ℕ
  length x = {!!}

{-
proof
   ?
   ≅⟨ ? ⟩
   ?
   ≅⟨ ? ⟩
   ?
   ≅⟨ ? ⟩
   ?
   ∎

-}
