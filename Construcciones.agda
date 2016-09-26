
module Construcciones where

open import Library hiding (_×_ ; swap)
open import Categories
open import Categories.Products
open import Categories.Terminal

open import Categories.Iso
-- Alt - * vuelve al lugar donde hiciste click
module TerminalIso {a}{b}(C : Cat {a}{b}) where
  open Terminal
  open Cat C
 

  {- Dos objetos terminales son isomorfos -}
  TerminalIso : (T T' : Obj)
            → (p : Terminal C T)
            → (q : Terminal C T')
            → Iso C (t p)
  TerminalIso T T' p q = iso (t q) 
                             (proof
                             (t p) ∙ (t q) 
                             ≅⟨ sym (law p) ⟩
                             t p                             
                             ≅⟨ law p ⟩
                             iden
                             ∎) 
                             (proof
                             (t q) ∙ (t p) 
                             ≅⟨ sym (law q) ⟩
                             t q                             
                             ≅⟨ law q ⟩
                             iden
                             ∎)

module SetStructure {l : Level} where

 open import Categories.Sets
{- Ejercicios
   -- Probar que Sets tiene objeto teminal y productos
-}

 SetsHasProducts : Products (Sets {l}) 
 SetsHasProducts = prod Library._×_ 
                        fst 
                        snd 
                        (λ f g x → (f x) , (g x)) 
                        refl
                        refl 
                        (λ {A}{B}{C}{f}{g}{h} -> λ p q → 
                        ext (λ c → cong₂ _,_  (cong-app p c) (cong-app q c)))
 OneSet : Terminal Sets ⊤
 OneSet = term (λ x → ⊤.tt) refl

{- Ejercicio EXTRA: Analizar si la categoría de pointed sets
   tiene producto y objeto terminal, en cuyo caso definirlo
-}


{- Dos productos de los mismos objetos son isomorfos -}
module ProductIso {a}{b}(C : Cat {a}{b}) where

  open Cat C

  open Products

  ProductIso : ∀{A B} → (p q : Products C)
           → Iso C (⟨_,_⟩ p {A} {B} (π₁ q) (π₂ q))
  ProductIso p q = iso (⟨_,_⟩ q (π₁ p) (π₂ p)) 
                       {!proof
                       ⟨ p , π₁ q ⟩ (π₂ q) ∙ ⟨ q , π₁ p ⟩ (π₂ p) 
                       ≅⟨ ? ⟩
                       iden
                       ∎!} 
                       {!!}

module ProductMorphisms {a}{b}{C : Cat {a}{b}}(p : Products C) where

  open Cat C
  open Products p

  {- Toda categoría con productos posee los siguientes morfismos -}
  swap : ∀{A B} → Hom (A × B)  (B × A)
  swap = {!!}

  assoc : ∀{A B C} → Hom ((A × B) × C) (A × (B × C))
  assoc = {!!}

  -- Probar que swap y assoc son isomorfismos.


  {- Definir el morfismo pair -}
  pair : ∀{A B C D}(f : Hom A B)(g : Hom C D)
       → Hom (A × C) (B × D)
  pair f g = {!!}

  -- Probar las siguientes propiedades de pair

  idpair : ∀{X} → pair (iden {X}) (iden {X}) ≅ iden {X × X}
  idpair {X} = {!!}

  compdistrib : ∀{A B C D E F}
              → (f : Hom B C)(g : Hom A B)
              → (h : Hom E F)(i : Hom D E)
              → pair (f ∙ g) (h ∙ i) ≅ pair f h ∙ pair g i
  compdistrib f g h i = {!!}

  open import Categories.ProductCat
  open import Functors

  -- Probar que el producto de objetos _×_, junto con pair
  -- forman un funtor C ×C C → C
  
--------------------------------------------------

