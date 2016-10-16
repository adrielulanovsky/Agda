
open import Categories
open import Functors

module Functors.Algebra {a}{b}{C : Cat {a}{b}}(F : Fun C C) where

open import Library

--------------------------------------------------
-- Suponemos que trabajamos con una categoría C dada y
-- un endofunctor F sobre ella
--------------------------------------------------
open Cat C
open Fun F

--------------------------------------------------
-- Una F-algebra es un objeto X de la categoría base
-- y una función F X → X

record F-algebra : Set (a ⊔ b) where
   constructor falgebra
   field
      carrier : Obj
      algebra : Hom (OMap carrier) carrier 

open F-algebra public


--------------------------------------------------
{- Un homomorfismo de álgebras <A,α> → <B,β> consiste en:
    un morfismo h entre los portadores de las algebras A → B
    una prueba de que se preserva la estructura:

        FA ----HMap F h ----> FB
        |                      |
        α                      β
        |                      |
        V                      V
        a-----------h--------> B
-}

record F-homomorphism (f g : F-algebra): Set (a ⊔ b) where
   constructor homo
   field
      homo-base : Hom (carrier f) (carrier g)
      homo-prop :  homo-base  ∙ algebra f ≅ algebra g ∙ HMap (homo-base) 

open F-homomorphism

--------------------------------------------------
{- Como es usual definimos cuando dos morfismos en la categoría
   son iguales: en este caso serán iguales si sus respectivos morfismos
   de C (homo-base) son iguales.
-}

homomorphismEq : {x y : F-algebra}
              → {h k : (F-homomorphism) x y}
              → homo-base h ≅ homo-base k
              → h ≅ k  
homomorphismEq {h = homo homo-base homo-prop} {homo .homo-base homo-prop₁} refl =
                                cong (homo homo-base) (ir homo-prop homo-prop₁)

-- si son iguales, sus bases son iguales
homomorphismCong : {x y : F-algebra}
              → {h k : (F-homomorphism) x y}
              → h ≅ k
              → homo-base h ≅ homo-base k  
homomorphismCong refl = refl
--------------------------------------------------
{- La identidad es un homomorfismo -}

iden-homo : {h : F-algebra} → (F-homomorphism) h h
iden-homo {h} = homo iden (proof
                           iden ∙ algebra h
                           ≅⟨ idl ⟩
                           algebra h
                           ≅⟨ sym idr ⟩
                           algebra h ∙ iden
                           ≅⟨ sym (congr fid) ⟩
                           algebra h ∙ HMap iden
                           ∎)

--------------------------------------------------
{- La composición de homomorfismo es un homomorfismo -}
--composition of homomorphisms
comp-homo : {x y z : F-algebra} 
             → (F-homomorphism) y z
             → (F-homomorphism) x y
             → (F-homomorphism) x z
comp-homo {x}{y}{z}(homo h p) (homo k q) = homo (h ∙ k) 
                                                (proof
                             (h ∙ k) ∙ algebra x
                             ≅⟨ ass ⟩
                             h ∙ k ∙ algebra x
                             ≅⟨ congr q ⟩
                             h ∙ algebra y ∙ HMap k
                             ≅⟨ sym ass ⟩
                             (h ∙ algebra y) ∙ HMap k
                             ≅⟨ congl p ⟩
                             (algebra z ∙ HMap h) ∙ HMap k
                             ≅⟨ ass ⟩
                             algebra z ∙ HMap h ∙ HMap k
                             ≅⟨ congr (sym fcomp) ⟩
                             algebra z ∙ HMap (h ∙ k)
                             ∎)

--------------------------------------------------
{- Con todo lo anterior podemos definir la categoría de
   F-Algebras.
-}

F-AlgebraCat : Cat
F-AlgebraCat = record
                   { Obj  = F-algebra
                   ; Hom  = F-homomorphism
                   ; iden = iden-homo
                   ; _∙_  = comp-homo
                   ; idl  = homomorphismEq idl
                   ; idr  = homomorphismEq idr
                   ; ass  = homomorphismEq ass
                   }
                   
--------------------------------------------------
{- Mapear un algebra <X,h> bajo un funtor
   es un algebra <FX, _> -}

mapF : F-algebra → F-algebra
mapF (falgebra x h) = falgebra (OMap x) (HMap h)

--------------------------------------------------

open import Categories.Initial

{- Suponemos que la categoría tiene un álgebra inicial
(en general esto depende de F, pero siempre existe para
 los funtores polinomiales)
-}
postulate inF : F-algebra
postulate F-initiality : Initial F-AlgebraCat inF

-- Por comodidad nombramos los componentes del álgebra inicial
open Initial F-initiality renaming (i to init-homo ; law to univ) public
open F-algebra inF renaming (carrier to μF ; algebra to α) public

{- El fold se obtiene (en forma genérica) usando algebras iniciales -}
fold : ∀{X : Obj} → (f : Hom (OMap X) X) → Hom μF X 
fold {X} f = homo-base (init-homo { falgebra X f })

{- El algebra inicial es un homomorfismo -}
α-homo : F-homomorphism (mapF inF) inF
α-homo = homo α refl

--------------------------------------------------
{- Lema de Lambek -}
{- El álgebra inicial es un isomorfismo -}

open import Categories.Iso

lemma : comp-homo α-homo init-homo ≅ iden-homo {inF}
lemma = proof
   comp-homo α-homo init-homo
   ≅⟨ sym (univ {f = comp-homo α-homo init-homo}) ⟩
   init-homo
   ≅⟨ univ {f = iden-homo} ⟩
   iden-homo
   ∎
   
lemma2 : comp-homo (init-homo {mapF inF}) α-homo ≅ iden-homo {mapF inF}
lemma2 = homomorphismEq (proof
   homo-base (comp-homo init-homo α-homo)
   ≅⟨ homo-prop (init-homo {mapF inF}) ⟩
   HMap (homo-base α-homo) ∙ HMap (homo-base init-homo)
   ≅⟨ sym fcomp ⟩
   HMap (homo-base (comp-homo α-homo init-homo))
   ≅⟨ cong HMap (homomorphismCong lemma) ⟩
   HMap iden
   ≅⟨ fid ⟩
   iden {carrier (mapF inF)}
   ≅⟨ refl ⟩
   homo-base (iden-homo {mapF inF})
   ∎)

L : Iso F-AlgebraCat α-homo
L = iso init-homo
        lemma
        lemma2
