module Categories where

{- importamos definición de igualdad heterogénea (y otras cosas) -}
open import Library

--------------------------------------------------
{- Definición de Categoría -}
{-
 - Una colección de objetos
 - Conjuntos de flechas entre objetos
 - todo objeto tiene una flecha identidad
 - todo par de flechas "compatibles" puede componerse
 - la composición es asociativa, con la flecha identidad como unidad.
-}

record Cat : Set₂ where
  infix 7 _∙_
  field Obj  : Set₁
        Hom  : Obj → Obj → Set
        iden : ∀{X} → Hom X X
        _∙_ : ∀{X Y Z} → Hom Y Z → Hom X Y → Hom X Z
        idl  : ∀{X Y}{f : Hom X Y} → iden ∙ f ≅ f
        idr  : ∀{X Y}{f : Hom X Y} → f ∙ iden ≅ f
        ass  : ∀{W X Y Z}{f : Hom Y Z}{g : Hom X Y}{h : Hom W X} → 
               (f ∙ g) ∙ h ≅  f ∙ (g ∙ h)
               

--------------------------------------------------
{- El típico ejemplo de categoría es la categoría Set de conjuntos y
   funciones entre los mismos.
-}

Sets : Cat
Sets = record
         { Obj = Set
         ; Hom = λ X Y → X → Y
         ; iden = id
         ; _∙_ = λ f g → f ∘ g
         ; idl = refl
         ; idr = refl
         ; ass = refl
         }








--------------------------------------------------
{- Para cada categoría existe la categoría dual, que consiste de los
mismos objetos, pero con las flechas invertidas. -}

_Op : Cat → Cat
C Op = let open Cat C in
       record
         { Obj = Obj
         ; Hom = λ X Y → Hom Y X
         ; iden = iden
         ; _∙_ = λ f g → g ∙ f
         ; idl = idr
         ; idr = idl
         ; ass = sym ass
         }











--------------------------------------------------
{- Categoría Discreta

   Una categoría discreta es una categoría en la que los únicos
morfismos son identidades. La composición y ecuaciones de coherencia
son triviales.
-}

Discrete :  Set → Cat
Discrete X = record
               { Obj = {!Lift X!}
               ; Hom = λ X Y → {!X ≅ Y!}
               ; iden = {!!}
               ; _∙_ = {!!}
               ; idl = {!!}
               ; idr = {!!}
               ; ass = {!!}
               }







{- A menudo nos queremos "olvidar" de los morfismos de una
categoría. Es decir, miramos a la categoría como una categoría
discreta. Esto se nota en lenguaje categórico como |C| -}

∣_∣ : Cat → Cat
∣ C ∣ = {!!}

--------------------------------------------------
{- Categoría Producto -}
{- Dadas dos categorías, podemos formar la categoría producto 
   Los objetos son el producto cartesiano de los objetos
   Los morfismos son pares de flechas.
-}

_×C_ : Cat → Cat → Cat
C ×C D = let open Cat in record
           { Obj = Obj C × Obj D
           ; Hom = λ X Y →  Hom C (fst X) (fst Y) × Hom D (snd X) (snd Y)
           ; iden = (iden C) , (iden D)
           ; _∙_ = λ f g → (_∙_ C (fst f) (fst g)) , (_∙_ D (snd f) (snd g))
           ; idl = cong₂ _,_ (idl C) (idl D)
           ; idr = cong₂ _,_ (idr C) (idr D)
           ; ass = cong₂ _,_ (ass C) (ass D)
           }









--------------------------------------------------
{- Familia de Conjuntos -}
{- Los objetos son familias de conjuntos
   (conjuntos indexados por un conjunto de índices)

  Los morfismos son funciones que preservan el índice.
-}

Fam : Set → Cat
Fam I = record
          { Obj = I → Set
          ; Hom = λ X Y → ∀{i} → X i → Y i 
          ; iden = id
          ; _∙_ = λ f g → f ∘ g
          ; idl = refl
          ; idr = refl
          ; ass = refl
          }

--------------------------------------------------
{- Ejemplo extendido: Categorías Slice -}

{- Dada una categoría C, los objetos de un slice
   sobre un objeto I, son morfismos con codominio I
-}

module Slice (C : Cat) where

 open Cat C

 record Slice₀ (I : Obj) : Set₁ where
  constructor _,_
  field
     base : Obj
     morObj : Hom base I

 open Slice₀

 {- record para representar los morfismos de la categoría -}
 record Slice₁ (I : Obj)(X Y : Slice₀ I) : Set where
  constructor _,_
  field
    baseHom : Hom (base X) (base Y)
    prop :  (morObj Y) ∙ baseHom ≅ morObj X
      
     {- para probar que dos morfismos de slice son iguales no nos
        interesa cual es la prueba de pro.  Cualquier prueba es
        suficiente
     -}

 open Slice₁






 {- veamos como funciona proof irrelevance -}
 Slice₁-eq : {I : Obj}{X Y : Slice₀ I}
          → {f g : Slice₁ I X Y}
          → baseHom f ≅ baseHom g
          → f ≅ g
 Slice₁-eq {f = f , p} {.f , q} refl = cong (_,_ f) (ir p q)








 {- la composición es simplemente pegar triángulos -}
 Slice-comp : {I : Obj}
             → {X Y Z :  Slice₀ I}
             → Slice₁ I Y Z --Hom Y Z
             → Slice₁ I X Y --Hom X Y
             → Slice₁ I X Z --Hom X Z
 Slice-comp {X = X , fx} {Y , fy} {Z , fz} (f , p) (g , q) =
                      (f ∙ g) , (proof
                      fz ∙ (f ∙ g)
                      ≅⟨ sym ass ⟩
                      (fz ∙ f) ∙ g
                      ≅⟨ cong₂ _∙_ p refl ⟩
                      fy ∙ g
                      ≅⟨ q ⟩
                      fx
                      ∎)




 Slice : (I : Obj) → Cat
 Slice I = record
              { Obj = Slice₀ I
              ; Hom = Slice₁ I
              ; iden = iden , idr
              ; _∙_ = Slice-comp
              ; idl = Slice₁-eq idl
              ; idr = Slice₁-eq idr
              ; ass = Slice₁-eq ass
              }

--------------------------------------------------

{- Ejercicio: Definir la categoría con un sólo objeto ⊤, y que sus
morfismos son los elementos de un monoide M -}

module ⊤-Cat where

  open import Records

  ⊤-Cat : Monoid -> Cat
  ⊤-Cat M = record
              { Obj = Lift ⊤
              ; Hom = λ X Y → Carrier
              ; iden = ε
              ; _∙_ = _∙_
              ; idl = lid
              ; idr = rid
              ; ass = assoc
              }
              where open Monoid M


--------------------------------------------------
{- Ejercicio: Definir la categoría en que los objetos son monoides,
  y las flechas son homomorfismos de monoides
-}

module MonCat where

  open import Records hiding (Iso)
  open Monoid-Homomorphism
  open Monoid

 {- record para representar los morfismos de la categoría -}
  record MonCat₁ (X Y : Monoid) : Set where
    constructor _,_
    field
      baseHom : Carrier X -> Carrier Y
      prop : Is-Monoid-Homo {X} {Y} baseHom   

  open MonCat₁

  comp-MonCat : {X Y Z : Monoid} → MonCat₁ Y Z → MonCat₁ X Y → MonCat₁ X Z
  comp-MonCat {X}{Y}{Z}(f , p) (g , q) = 
                     let 
                       open Monoid X renaming (ε to ε₁ ;  _∙_ to _∙1_)
                       open Monoid Y renaming (ε to ε₂ ;  _∙_ to _∙2_)
                       open Monoid Z renaming (ε to ε₃ ;  _∙_ to _∙3_)
                       open Is-Monoid-Homo renaming (preserves-unit to u1; preserves-mult to m1)
                     in (f ∘ g) , record { preserves-unit = (proof
                                                              f (g ε₁)
                                                              ≅⟨ cong f (u1 q) ⟩
                                                              f ε₂
                                                              ≅⟨ u1 p ⟩
                                                              ε₃
                                                              ∎)
                                         ; preserves-mult = λ {x}{y} ->
                                                             (proof
                                                              f (g (x ∙1 y))
                                                              ≅⟨ cong f (m1 q) ⟩
                                                              f ((g x) ∙2 (g y))
                                                              ≅⟨ m1 p ⟩
                                                              f (g x) ∙3 f (g y)
                                                              ∎) }

  Is-Homo-eq : {M N : Monoid} -> {f : Carrier M -> Carrier N} ->
               {x y : Is-Monoid-Homo {M} {N} f} -> x ≅ y
  Is-Homo-eq {x = record 
                    { preserves-unit = u1 
                    ; preserves-mult = m1 }} 
                 {record 
                    { preserves-unit = u2 
                     ; preserves-mult = m2 }} = 
                proof
                  record { preserves-unit = u1 ; preserves-mult = m1 } 
                  ≅⟨ cong₂ is-monoid-homo (ir u1 u2) (i2ir m1 m2) ⟩
                  record { preserves-unit = u2 ; preserves-mult = m2 }
                ∎


  MonCat-eq : {X Y : Monoid} → {f g : MonCat₁ X Y}
            → baseHom f ≅ baseHom g → f ≅ g
  MonCat-eq {f = f , p} {.f , q} refl = 
                                cong ((_,_) f) ((Is-Homo-eq {f = f} {p} {q}))

{-  MonCat-idl : {X Y : Monoid} {f : MonCat₁ X Y} →
      comp-MonCat (id , is-monoid-homo refl (λ {x} {y} → refl)) f ≅ f
  MonCat-idl = {!!}
-}

  MonCat : Cat
  MonCat = record
             { Obj = Monoid
             ; Hom = MonCat₁
             ; iden = id , record { preserves-unit = refl 
                                  ; preserves-mult = refl }
             ; _∙_ = comp-MonCat
             ; idl = {!!}
             ; idr = {!!}
             ; ass = {!!}
             }
            where open Monoid
--------------------------------------------------
{- Ejercicio: Dada un categoría C, definir la siguiente categoría:
  - Los objetos son morfismos de C
  - Un morfismo entre una flecha f: A → B y f': A'→ B' es un par de morfismos de C
      g1 : A → A', y g2 : B → B', tal que
                    f' ∙ g₁ ≅ g₂ ∙ f
-}








--------------------------------------------------
{- Generalizamos la noción de isomorfismo de la clase pasada a cualquier categoría -}

{- Isomorfismo en una categoría -}

open Cat

record Iso {C : Cat}(A B : Obj C)(fun : Hom C A B) : Set where
  constructor iso
  field inv : Hom C B A
        law1 : _∙_ C fun inv  ≅ iden C {B}
        law2 : _∙_ C inv fun  ≅ iden C {A}

--------------------------------------------------

{- Ejercicio
 Mostrar que en el caso de la categoría Sets, isomorfismo corresponde a biyección de funciones

Ayuda : puede ser útil usar cong-app
-}

Biyectiva : {X Y : Set}(f : X → Y) → Set
Biyectiva {X} {Y} f = (y : Y) → Σ X (λ x → (f x ≅ y) × (∀ x' → f x' ≅ y → x ≅ x')) 



--------------------------------------------------
{- Ejercicio:
 Probar que un isormofismo en (C : Cat) es un isomorfismo en (C Op).
-}

--------------------------------------------------
{- Ejercicio EXTRA:
 Definir la categoría de pointed sets:
  - objetos son conjuntos junto con un elemento designado del conjunto.
     Por ejemplo (Bool , false), (ℕ , 0) , etc.
  - los morfismos son funciones entre los conjuntos que preservan el punto
     (A,a) → (B, b) es una función f : A → B, tal que f(a) = b 
-}

--------------------------------------------------

{- Ejercicio EXTRA:
 Definir la categoría cuyos
  - objetos son conjuntos finitos (y por lo tanto isomorfos a Fin n para algún n)
  - morfismos son isomorfismos.  
-}

--------------------------------------------------
