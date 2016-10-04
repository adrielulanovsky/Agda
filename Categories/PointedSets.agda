{- Ejercicio EXTRA:
 Definir la categoría de pointed sets:
  - objetos son conjuntos junto con un elemento designado del conjunto.
     Por ejemplo (Bool , false), (ℕ , 0) , etc.
  - los morfismos son funciones entre los conjuntos que preservan el punto
     (A,a) → (B, b) es una función f : A → B, tal que f(a) = b 
-}

module Categories.PointedSets where
  open import Library
  open import Categories

  record PointedSets₀ : Set₁ where
    constructor _,_
    field
      conj : Set
      elem : conj
      
  open PointedSets₀

  record PointedSets₁ (X Y : PointedSets₀) : Set where
    constructor _&_
    field
      fun : conj X -> conj Y
      prop :  fun (elem X) ≅ elem Y

  open PointedSets₁

  _**_ : {X Y Z : PointedSets₀} →
      PointedSets₁ Y Z → PointedSets₁ X Y → PointedSets₁ X Z
  _**_ {A , a} {B , b} {C , c} (f & p) (g & q) = (f ∘ g) & (proof
                          f (g a)
                          ≅⟨ cong f q ⟩
                          f b
                          ≅⟨ p ⟩
                          c
                          ∎)
                          
  PointedSets-eq : {X Y : PointedSets₀} → {f g : PointedSets₁ X Y}
                   → fun f ≅ fun g → f ≅ g
  PointedSets-eq {f = f & p} {.f & q} refl = cong₂ _&_ refl (ir p q)

  PointedSets : Cat
  PointedSets = record
             { Obj = PointedSets₀
             ; Hom = PointedSets₁
             ; iden = (id & refl)
             ; _∙_ = _**_
             ; idl = PointedSets-eq refl
             ; idr = PointedSets-eq refl
             ; ass = PointedSets-eq refl
             }
