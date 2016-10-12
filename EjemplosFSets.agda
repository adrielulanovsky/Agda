
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


  -- definir constructores
  0N : μF
  0N = (α ∘ inl) ⊤.tt

  0N2 : ⊤ -> μF
  0N2 x = 0N

  sucN : μF → μF
  sucN x = (α ∘ inr) x

{- Probar que el portador de la semántica de algebra inicial
  de OnePlus es igual a ℕ

Nota: quiero probar que μF es isomorfo a ℕ
-}
  Natμ : ℕ -> μF
  Natμ zero = 0N
  Natμ (suc x) = sucN (Natμ x)
 
  FNat-Nat : (OMap ℕ) -> ℕ
  FNat-Nat (Inl x) = 0
  FNat-Nat (Inr x) = suc x
  
  lemmaNat1 : (x : ℕ) -> ((fold FNat-Nat) ∘ Natμ) x ≅ x
  lemmaNat1 = {!!}

  lemmaNat2 : Natμ ∘ (fold FNat-Nat) ≅ id
  lemmaNat2 = proof
                                 Natμ ∘ (fold FNat-Nat)
                                 ≅⟨ {!!} ⟩
                                 {!!}
                                 ≅⟨ {!!} ⟩
                                 homo-base init-homo
                                 ≅⟨ cong homo-base (univ {f = iden-homo}) ⟩
                                 homo-base (iden-homo {inF})
                                 ≅⟨ refl ⟩
                                 id
                                 ∎

  --intentar probar que [zero, suc] es un f-algebra inicial  

  lemaNat : Iso Sets (fold FNat-Nat)
  lemaNat = iso Natμ 
                {!!} 
                {!!}

--------------------------------------------------
{- Definir un functor cuya algebra inicial sea las listas.
-}

L : (A : Set) → Fun Sets Sets
L A = {!!}

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
  length = {!!}

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