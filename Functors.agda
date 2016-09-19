module Functors where

open import Library
open import Categories
open Cat

{- Los Funtores proveen morfismos entre categorías
 Deben preservar la estructura de las mismas.
-}

record Fun (C : Cat)(D : Cat) : Set₁ 
  where
  constructor functor
  field OMap  : Obj C → Obj D
        HMap  : ∀{X Y} → Hom C X Y → Hom D (OMap X) (OMap Y)
        fid   : ∀{X} → HMap (iden C {X}) ≅ iden D {OMap X}
        fcomp : ∀{X Y Z}{f : Hom C Y Z}{g : Hom C X Y} → 
                HMap (_∙_ C f g) ≅ _∙_ D (HMap f) (HMap g)
open Fun

{- ¿Cómo se relaciona con la noción de Functor en Haskell? -}

--------------------------------------------------
{- Ejemplos -}
--------------------------------------------------

{- Funtor Identidad -}
IdF : ∀(C : Cat) → Fun C C
IdF C = functor (λ x → x) ((λ x → x)) refl refl

--------------------------------------------------
{- Functor Constante
  Mapea todo objeto de C en un objeto de D dado, y todo morfismo a la identidad.
-}

K : ∀{C D : Cat}(X : Cat.Obj D) → Fun C D
K {_} {D} X = functor (λ x → X) (λ x → iden D) refl (sym (idl D))
--------------------------------------------------
{- Funtor Diagonal
  Mapea X al objeto de la categoría producto (X , X)
-}

Δ : ∀{C : Cat} → Fun C (C ×C C)
Δ = functor (λ x → x , x) (λ f → f , f) refl refl
--------------------------------------------------
{- Funtores sobre la categoría Sets -}

{- Funtor cuadrado
  (notar la diferencia con el diagonal para la categoría Sets)
  Mapea X al producto cartesiano X × X
 -}
Cuadrado : Fun Sets Sets
Cuadrado = functor (λ A → A × A) (λ f A → f (fst A) , f (snd A)) refl refl

{- Funtor Producto
  Mapea un objeto de la categoría producto al producto cartesiano.
 -}
Producto : Fun (Sets ×C Sets) Sets
Producto = functor (λ A → (fst A) × (snd A)) (λ f A → ((fst f) (fst A)) , ((snd f) (snd A))) refl refl

-- Funtor Maybe
open import Data.Maybe.Base renaming (map to mapMaybe)

Maybe-fid : {X : Set}(x : Maybe X) -> mapMaybe id x ≅ x
Maybe-fid (just x) = refl
Maybe-fid nothing = refl

Maybe-fcomp : {X Y Z : Set}{g : X -> Y}{f : Y -> Z}(x : Maybe X) -> mapMaybe (f ∘ g) x ≅ ((mapMaybe f) ∘ (mapMaybe g)) x
Maybe-fcomp (just x) = refl
Maybe-fcomp nothing = refl

MaybeF : Fun Sets Sets
MaybeF = functor Maybe
                 mapMaybe
                 (ext Maybe-fid)
                 (ext Maybe-fcomp)

-- Funtor Lista 
open import Data.List.Base renaming (map to mapList)

ListF-fid : {X : Set}(x : List X) -> mapList id x ≅ x
ListF-fid [] = refl
ListF-fid (x ∷ xs) = cong (_∷_ x) (ListF-fid xs)

ListF-fcomp : {X Y Z : Set}{g : X -> Y}{f : Y -> Z}(x : List X) ->
              mapList (f ∘ g) x ≅ ((mapList f) ∘ (mapList g)) x
ListF-fcomp [] = refl
ListF-fcomp {g = g}{f}(x ∷ xs) = cong (_∷_ (f (g x))) (ListF-fcomp xs)

ListF : Fun Sets Sets
ListF = functor List
                mapList
                (ext ListF-fid)
                (ext ListF-fcomp)

--Bifuntor de árboles con diferente información en nodos y hojas
data Tree (A B : Set) : Set where
     leaf : A → Tree A B
     node : (lt : Tree A B) → B → (rt : Tree A B) → Tree A B

mapTree : ∀{A A' B B'} → (A → A') → (B → B') → Tree A B → Tree A' B'
mapTree f g (leaf x) = leaf (f x)
mapTree f g (node t1 x t2) = node (mapTree f g t1) (g x) ((mapTree f g t2))

module TreeF where

  open Cat (Sets ×C Sets) renaming (iden to ident; Obj to ObjT; Hom to HomT; _∙_ to _*_)

  TreeF-fid : {X : ObjT}(a : Tree (fst X) (snd X)) →
      mapTree (fst (ident {X})) (snd (ident {X})) a ≅ a
  TreeF-fid (leaf x) = refl
  TreeF-fid {X} (node t1 x t2) = proof
                              node (mapTree (fst (ident {X})) (snd (ident {X})) t1) (snd (ident {X}) x) (mapTree (fst (ident {X})) (snd (ident {X})) t2)
                              ≅⟨ cong (λ a -> node a (snd (ident {X}) x) (mapTree (fst (ident {X})) (snd (ident {X})) t2)) (TreeF-fid t1) ⟩
                              node t1 (snd (ident {X}) x) (mapTree (fst (ident {X})) (snd (ident {X})) t2)
                              ≅⟨ cong (λ a -> node t1 (snd (ident {X}) x) a) (TreeF-fid t2) ⟩
                              node t1 (snd (ident {X}) x) t2
                              ≅⟨ cong (λ a -> node t1 a t2) refl ⟩
                              node t1 x t2
                              ∎

  TreeF-fcomp : {X Y Z : ObjT}{f : HomT Y Z}{g : HomT X Y}(a : Tree (fst X) (snd X)) →  mapTree (fst (f * g)) (snd (f * g)) a ≅
                 mapTree (fst f) (snd f) (mapTree (fst g) (snd g) a) 
  TreeF-fcomp (leaf x) = refl
  TreeF-fcomp {f = f}{g}(node t1 x t2) = proof
      node (mapTree (fst (f * g)) (snd (f * g)) t1)
           (snd (f * g) x)
           (mapTree (fst (f * g)) (snd (f * g)) t2)
      ≅⟨ cong (λ a → node a (snd (f * g) x)
           (mapTree (fst (f * g)) (snd (f * g)) t2)) (TreeF-fcomp t1) ⟩
      node (mapTree (fst f) (snd f) (mapTree (fst g) (snd g) t1))
           (snd (f * g) x)
           (mapTree (fst (f * g)) (snd (f * g)) t2)
      ≅⟨ cong (λ a → node (mapTree (fst f) (snd f) (mapTree (fst g) (snd g) t1))
             (snd (f * g) x)
           a) (TreeF-fcomp t2) ⟩
      node (mapTree (fst f) (snd f) (mapTree (fst g) (snd g) t1))
           (snd (f * g) x)
           (mapTree (fst f) (snd f) (mapTree (fst g) (snd g) t2))
      
      ≅⟨ cong (λ a → node (mapTree (fst f) (snd f) (mapTree (fst g) (snd g) t1))
           a
           (mapTree (fst f) (snd f) (mapTree (fst g) (snd g) t2))
      ) refl ⟩
      node (mapTree (fst f) (snd f) (mapTree (fst g) (snd g) t1))
           (snd f (snd g x))
           (mapTree (fst f) (snd f) (mapTree (fst g) (snd g) t2))
      ∎

  TreeF : Fun (Sets ×C Sets) Sets
  TreeF = functor (λ x → Tree (fst x) (snd x))
                  (λ f t → mapTree (fst f) (snd f) t)
                  (ext TreeF-fid)
                  (ext TreeF-fcomp)

--------------------------------------------------
{- Hom functor : probar que el Hom de una categoría C
  es un bifunctor Hom : (C Op) ×C C → Sets
  -}
module BifunctorHom (C : Cat) where
  open Cat C renaming (Obj to ObjC; Hom to HomC; _∙_ to _**_; iden to idenC; idl to idlC)
  open Cat ((C Op) ×C C) renaming (Obj to ObjCxC; iden to idenCxC; idl to idlCxC)

  fstIsIden : {X : ObjCxC} -> fst (idenCxC {X}) ≅ idenC {fst X}
  fstIsIden = {!idenCxC!}

  BifunctorHom : Fun ((C Op) ×C C) Sets
  OMap BifunctorHom (x , y) = HomC x y
  HMap BifunctorHom (f1 , f2) g = f2 ** (g ** f1)
--  fid BifunctorHom {x1 , x2} with idenCxC {x1 , x2}
--  fid BifunctorHom {x1 , x2} | id1 , id2 = ext {!!}
{-ext (λ a → proof
                                           snd idenCxC ** (a ** fst idenCxC)
                                           ≅⟨ {!idlC!} ⟩
                                           a
                                           ∎)-}
  fid BifunctorHom {x1 , x2} = ext (λ a → proof
                                           snd idenCxC ** (a ** fst idenCxC)
                                           ≅⟨ {!idlC!} ⟩
                                           a
                                           ∎)
  fcomp BifunctorHom = {!!}

--------------------------------------------------
{- Composición de funtores -}
_○_ : ∀{C : Cat}{D : Cat}{E : Cat} → 
      Fun D E → Fun C D → Fun C E
functor OMap1 HMap1 fid1 fcomp1 ○ functor OMap2 HMap2 fid2 fcomp2 = functor (OMap1 ∘ OMap2)
    (HMap1 ∘ HMap2)
    (trans (cong HMap1 fid2) fid1)
    (trans (cong HMap1 fcomp2) fcomp1)
infixr 10 _○_

--------------------------------------------------
{- ¿Cuándo dos funtores son iguales ?
  Cuando
  1. el mapeo de objetos es igual
  2. Para cualquier par de objetos X,Y, el mapeo de Hom(X,Y) es el mismo

  Notar que las pruebas de las propiedades no son relevantes.
-}
FunctorEq : ∀{C : Cat}{D : Cat}
         →  (F G : Fun C D)
         →  OMap F ≅ OMap G
         →  (λ {X Y} → HMap F {X}{Y}) ≅ (λ {X}{Y} → HMap G {X}{Y})
         → F ≅ G
FunctorEq (functor OMap1 HMap1 fid1 fcomp1) (functor .OMap1 .HMap1 fid2 fcomp2) refl refl = 
                         proof
                         functor OMap1 HMap1 fid1 fcomp1
                         ≅⟨ cong₂ (functor OMap1 HMap1) (iir fid1 fid2) 
                           (iext (λ a → iext (λ a₁ → iext (λ a₂ → i2ir fcomp1 fcomp2)))) ⟩
                         functor OMap1 HMap1 fid2 fcomp2
                         ∎
--------------------------------------------------

{- Categoría (grande) de categorías chicas Dado que tenemos un funtor
  identidad, y que la composición de funtores es un funtor, tenemos
  una categoría CAT, cuyos objetos son categorías, y sus flechas son
  funtores.
-}

{-
CAT : Cat
CAT = record
           { Obj = Cat
           ; Hom = Fun
           ; iden = IdF
           ; _∙_ = _○_
           ; idl = FunctorEq refl refl
           ; idr = FunctorEq refl refl
           ; ass = FunctorEq refl refl
           }
-}


--------------------------------------------------

{- Ejercicio: Probar que los funtores preservan isomorfismos Es decir,
que si tenemos un funtor F : C → D, y f es un componente de un
isomorfismo en C, entonces (HMap F f) es un isomotfismo en D.

-}

open Iso

FunIso : ∀{C D}(F : Fun C D){X Y}{f : Cat.Hom C X Y}
       → Iso {C} X Y f → Iso {D} _ _ (HMap F f)
FunIso (functor OMap HMap fid fcomp) {f = f} (iso inv law1 law2) =
       iso (HMap inv) (trans (sym fcomp) (trans (cong HMap law1) fid)) (trans (sym fcomp) (trans (cong HMap law2) fid))

--------------------------------------------------

{- Ejercicio EXTRA: En una clase anterior definimos un Monoide M como
   categoría (MonCat M) con un solo objeto.  Probar que dar funtor F :
   (MonCat M) → (MonCat N) es equivalente a dar un homomorfismo de
   monoides entre M y N.

-}


