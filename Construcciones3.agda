
module Construcciones3 where

open import Library hiding (_×_ ; swap)
open import Categories
open import Categories.Products
open import Categories.Terminal

open import Categories.Iso
-- Alt - * vuelve al lugar donde hiciste click
-- C-u C-u C-c C-, normaliza el goal
-- C-c C-s solve, te llena el inicio y fin de la prueba
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
module PointedSetsProduct where
  open import Categories.PointedSets
  open Products
  open PointedSets₀
  open PointedSets₁
  
{-  PointedSetsHasProducts : Products PointedSets  
  PointedSetsHasProducts = prod (λ A B → (Library._×_ (conj A) (conj B)) , ((elem A) , (elem B)))
                                (fst & refl)
                                (snd & refl)
                                (λ f g → (λ x → (fun f x) , fun g x) & cong₂ (_,_) (prop f) (prop g))
                                (PointedSets-eq refl)
                                (PointedSets-eq refl)
                                (λ {A}{B}{C}{f}{g}{h} -> λ p q → PointedSets-eq (ext (λ a → proof
                       fun h a
                       ≅⟨ refl ⟩
                       (fst (fun h a) , snd (fun h a))
                       ≅⟨ {!!} ⟩
                       (fun f a , fun g a)
                       ∎)) )
  -}
  OnePointedSet : Terminal PointedSets (⊤ , ⊤.tt)
  OnePointedSet = term ((λ x → ⊤.tt) & refl) (PointedSets-eq (ext (λ a → refl)))

{- Dos productos de los mismos objetos son isomorfos -}
module ProductIso {a}{b}(C : Cat {a}{b}) where

  open Cat C

  open Products
  ProductIso : ∀{A B} → (p q : Products C)
           → Iso C (⟨_,_⟩ p {A} {B} (π₁ q) (π₂ q))
  ProductIso p q = iso (⟨_,_⟩ q (π₁ p) (π₂ p)) 
                       (proof
                       ⟨ p , π₁ q ⟩ (π₂ q) ∙ ⟨ q , π₁ p ⟩ (π₂ p) 
                       ≅⟨ law3 p
           (proof
           π₁ p ∙ ⟨ p , π₁ q ⟩ (π₂ q) ∙ ⟨ q , π₁ p ⟩ (π₂ p)
           ≅⟨ sym ass ⟩
           (π₁ p ∙ ⟨ p , π₁ q ⟩ (π₂ q)) ∙ ⟨ q , π₁ p ⟩ (π₂ p)
           ≅⟨ cong (λ x -> x ∙ ⟨ q , π₁ p ⟩ (π₂ p) ) (law1 p) ⟩
           π₁ q ∙ ⟨ q , π₁ p ⟩ (π₂ p)
           ≅⟨ law1 q ⟩
           π₁ p
           ∎)
           (proof
           π₂ p ∙ ⟨ p , π₁ q ⟩ (π₂ q) ∙ ⟨ q , π₁ p ⟩ (π₂ p)
           ≅⟨ sym ass ⟩
           (π₂ p ∙ ⟨ p , π₁ q ⟩ (π₂ q)) ∙ ⟨ q , π₁ p ⟩ (π₂ p)
           ≅⟨ cong (λ x -> x ∙ ⟨ q , π₁ p ⟩ (π₂ p) ) (law2 p) ⟩
           π₂ q ∙ ⟨ q , π₁ p ⟩ (π₂ p)
           ≅⟨ law2 q ⟩
           π₂ p
           ∎) ⟩
                       ⟨ p , π₁ p ⟩ (π₂ p)
                       ≅⟨ sym (law3 p idr idr) ⟩
                       iden
                       ∎) 
                       ((proof
                       ⟨ q , π₁ p ⟩ (π₂ p) ∙ ⟨ p , π₁ q ⟩ (π₂ q) 
                       ≅⟨ law3 q 
           (proof
           π₁ q ∙ ⟨ q , π₁ p ⟩ (π₂ p) ∙ ⟨ p , π₁ q ⟩ (π₂ q)
           ≅⟨ sym ass ⟩
           (π₁ q ∙ ⟨ q , π₁ p ⟩ (π₂ p)) ∙ ⟨ p , π₁ q ⟩ (π₂ q)
           ≅⟨ cong (λ x -> x ∙ ⟨ p , π₁ q ⟩ (π₂ q) ) (law1 q) ⟩
           π₁ p ∙ ⟨ p , π₁ q ⟩ (π₂ q)
           ≅⟨ law1 p ⟩
           π₁ q
           ∎) 
           (proof
           π₂ q ∙ ⟨ q , π₁ p ⟩ (π₂ p) ∙ ⟨ p , π₁ q ⟩ (π₂ q)
           ≅⟨ sym ass ⟩
           (π₂ q ∙ ⟨ q , π₁ p ⟩ (π₂ p)) ∙ ⟨ p , π₁ q ⟩ (π₂ q)
           ≅⟨ cong (λ x -> x ∙ ⟨ p , π₁ q ⟩ (π₂ q) ) (law2 q) ⟩
           π₂ p ∙ ⟨ p , π₁ q ⟩ (π₂ q)
           ≅⟨ law2 p ⟩
           π₂ q
           ∎) 
                        ⟩
                       ⟨ q , π₁ q ⟩ (π₂ q)
                       ≅⟨ sym (law3 q idr idr) ⟩
                       iden
                       ∎))

module ProductMorphisms {a}{b}{C : Cat {a}{b}}(p : Products C) where

  open Cat C
  open Products p

  {- Toda categoría con productos posee los siguientes morfismos -}
  swap : ∀{A B} → Hom (A × B)  (B × A)
  swap = ⟨ π₂ , π₁ ⟩

  assoc : ∀{A B C} → Hom ((A × B) × C) (A × (B × C))
  assoc = λ {A} {B} {C} → ⟨ π₁ ∙ π₁ , ⟨ π₂ ∙ π₁ , π₂ ⟩ ⟩

  -- Probar que swap y assoc son isomorfismos
  assoc2 : ∀{A B C} → Hom (A × (B × C)) ((A × B) × C)
  assoc2 = λ {A} {B} {C} → ⟨ ⟨ π₁ , π₁ ∙ π₂ ⟩ , π₂ ∙ π₂ ⟩

  swapswap : ∀{A B} -> swap ∙ swap {A} {B} ≅ iden {A × B}
  swapswap = λ{A}{B} -> proof
                 swap ∙ swap
                 ≅⟨ law3 
      (proof
       π₁ ∙ swap ∙ swap
       ≅⟨ sym ass ⟩
       (π₁ ∙ swap) ∙ swap
       ≅⟨ cong (λ x -> x ∙ swap) law1 ⟩
       π₂ ∙ swap
       ≅⟨ law2 ⟩
       π₁
       ∎) 
      (proof
       π₂ ∙ swap ∙ swap
       ≅⟨ sym ass ⟩
       (π₂ ∙ swap) ∙ swap
       ≅⟨ cong (λ x -> x ∙ swap) law2 ⟩
       π₁ ∙ swap
       ≅⟨ law1 ⟩
       π₂
       ∎) 
                   ⟩
                 ⟨ π₁ , π₂ ⟩
                 ≅⟨ sym (law3 idr idr) ⟩
                 iden
                 ∎

  swapIso : ∀{A B} -> Iso C (swap {A} {B})
  swapIso = iso swap
                swapswap
                swapswap
  assocIso : ∀{A B D} -> Iso C (assoc {A} {B} {D})
  assocIso = iso assoc2
                 (proof
                 assoc ∙ assoc2
                 ≅⟨ law3
      (proof
      π₁ ∙ assoc ∙ assoc2
      ≅⟨ sym ass ⟩
      (π₁ ∙ assoc) ∙ assoc2
      ≅⟨ congl law1 ⟩
      (π₁ ∙ π₁) ∙ assoc2
      ≅⟨ ass ⟩
      π₁ ∙ π₁ ∙ assoc2
      ≅⟨ congr law1 ⟩
      π₁ ∙ ⟨ π₁ , π₁ ∙ π₂ ⟩
      ≅⟨ law1 ⟩
      π₁
      ∎)
      
      (proof
      π₂ ∙ assoc ∙ assoc2
      ≅⟨ sym ass ⟩
      (π₂ ∙ assoc) ∙ assoc2
      ≅⟨ congl law2 ⟩
      ⟨ π₂ ∙ π₁ , π₂ ⟩ ∙ assoc2
      ≅⟨ law3
    (proof
      π₁ ∙ ⟨ π₂ ∙ π₁ , π₂ ⟩ ∙ assoc2
      ≅⟨ sym ass ⟩
      (π₁ ∙ ⟨ π₂ ∙ π₁ , π₂ ⟩) ∙ assoc2
      ≅⟨ congl law1 ⟩
      (π₂ ∙ π₁) ∙ assoc2
      ≅⟨ ass ⟩
      π₂ ∙ π₁ ∙ assoc2
      ≅⟨ congr law1 ⟩
      π₂ ∙ ⟨ π₁ , π₁ ∙ π₂ ⟩
      ≅⟨ law2 ⟩
      π₁ ∙ π₂
      ∎ )
    (proof
      π₂ ∙ ⟨ π₂ ∙ π₁ , π₂ ⟩ ∙ assoc2
      ≅⟨ sym ass ⟩
      (π₂ ∙ ⟨ π₂ ∙ π₁ , π₂ ⟩) ∙ assoc2
      ≅⟨ congl law2 ⟩
      π₂ ∙ assoc2
      ≅⟨ law2 ⟩
      π₂ ∙ π₂
      ∎)
      ⟩
      ⟨ π₁ ∙ π₂ , π₂ ∙ π₂ ⟩
      ≅⟨ sym (law3 refl refl) ⟩
      π₂
      ∎)
                 ⟩
                 ⟨ π₁ , π₂ ⟩
                 ≅⟨ sym (law3 idr idr) ⟩
                 iden
                 ∎)
                 
                 (proof
                 assoc2 ∙ assoc
                 ≅⟨ law3
      (proof
      π₁ ∙ assoc2 ∙ assoc
      ≅⟨ sym ass ⟩
      (π₁ ∙ assoc2) ∙ assoc
      ≅⟨ congl law1 ⟩
      ⟨ π₁ , π₁ ∙ π₂ ⟩ ∙ assoc
      ≅⟨ law3
    (proof
      π₁ ∙ ⟨ π₁ , π₁ ∙ π₂ ⟩ ∙ assoc
      ≅⟨ sym ass ⟩
      (π₁ ∙ ⟨ π₁ , π₁ ∙ π₂ ⟩) ∙ assoc
      ≅⟨ congl law1 ⟩
      π₁ ∙ assoc
      ≅⟨ law1 ⟩
      π₁ ∙ π₁
      ∎)
    (proof
      π₂ ∙ ⟨ π₁ , π₁ ∙ π₂ ⟩ ∙ assoc
      ≅⟨ sym ass ⟩
      (π₂ ∙ ⟨ π₁ , π₁ ∙ π₂ ⟩) ∙ assoc
      ≅⟨ congl law2 ⟩
      (π₁ ∙ π₂) ∙ assoc
      ≅⟨ ass ⟩
      π₁ ∙ π₂ ∙ assoc
      ≅⟨ congr law2 ⟩
      π₁ ∙ ⟨ π₂ ∙ π₁ , π₂ ⟩
      ≅⟨ law1 ⟩
      π₂ ∙ π₁
      ∎)
      ⟩
      ⟨ π₁ ∙ π₁ , π₂ ∙ π₁ ⟩
      ≅⟨ sym (law3 refl refl) ⟩
      π₁
      ∎)
      (proof
      π₂ ∙ assoc2 ∙ assoc
      ≅⟨ sym ass ⟩
      (π₂ ∙ assoc2) ∙ assoc
      ≅⟨ congl law2 ⟩
      (π₂ ∙ π₂) ∙ assoc
      ≅⟨ ass ⟩
      π₂ ∙ π₂ ∙ assoc
      ≅⟨ congr law2 ⟩
      π₂ ∙ ⟨ π₂ ∙ π₁ , π₂ ⟩
      ≅⟨ law2 ⟩
      π₂
      ∎)
                 ⟩
                 ⟨ π₁ , π₂ ⟩
                 ≅⟨ sym (law3 idr idr) ⟩
                 iden
                 ∎)

  {- Definir el morfismo pair -}
  pair : ∀{A B C D}(f : Hom A B)(g : Hom C D)
       → Hom (A × C) (B × D)
  pair f g = ⟨ f ∙ π₁ , g ∙ π₂ ⟩

  -- Probar las siguientes propiedades de pair

  idpair : ∀{X Y} → pair (iden {X}) (iden {Y}) ≅ iden {X × Y}
  idpair {X} = proof
             pair iden iden
             ≅⟨ cong₂ ⟨_,_⟩ idl idl ⟩
             ⟨ π₁ , π₂ ⟩
             ≅⟨ sym (law3 idr idr) ⟩
             iden
             ∎

  compdistrib : ∀{A B C D E F}
              → (f : Hom B C)(g : Hom A B)
              → (h : Hom E F)(i : Hom D E)
              → pair (f ∙ g) (h ∙ i) ≅ pair f h ∙ pair g i
  compdistrib f g h i = proof
                      pair (f ∙ g) (h ∙ i)
                      ≅⟨ sym (law3 
             (proof
              π₁ ∙ pair f h ∙ pair g i
              ≅⟨ sym ass ⟩
              (π₁ ∙ pair f h) ∙ pair g i
              ≅⟨ cong (λ x -> x ∙ pair g i) law1 ⟩
              (f ∙ π₁) ∙ pair g i
              ≅⟨ ass ⟩
              f ∙ π₁ ∙ pair g i
              ≅⟨ cong₂ _∙_ refl law1 ⟩
              f ∙ g ∙ π₁
              ≅⟨ sym ass ⟩
              (f ∙ g) ∙ π₁
              ∎) 

             (proof
              π₂ ∙ pair f h ∙ pair g i
              ≅⟨ sym ass ⟩
              (π₂ ∙ pair f h) ∙ pair g i
              ≅⟨ cong (λ x -> x ∙ pair g i) law2 ⟩
              (h ∙ π₂) ∙ pair g i
              ≅⟨ ass ⟩
              h ∙ π₂ ∙ pair g i
              ≅⟨ cong₂ _∙_ refl law2 ⟩
              h ∙ i ∙ π₂
              ≅⟨ sym ass ⟩
              (h ∙ i) ∙ π₂
              ∎))
                      ⟩
                      pair f h ∙ pair g i
                      ∎

  open import Categories.ProductCat
  open import Functors

  -- Probar que el producto de objetos _×_, junto con pair
  -- forman un funtor C ×C C → C
  productIsFunctor : Fun (C ×C C) C
  productIsFunctor = functor (λ { (A , B) → A × B }) (λ { (f , g) → pair f g }) idpair (λ {X}{Y}{Z}{f}{g} -> compdistrib (fst f) (fst g) (snd f) (snd g))


--------------------------------------------------
