-- FormasNormales.hs
-- Formas normales.
-- José A. Alonso Jiménez https://jaalonso.github.com
-- =====================================================================

module FormasNormales where

-- ---------------------------------------------------------------------
-- § Introducción                                                     --
-- ---------------------------------------------------------------------

-- En este módulo se implementa el cálculo de la formas normales de
-- fórmulas proposicionales siguiendo su exposición en el tema 4 de la
-- asignatura de "Lógica informática" que se encuentra en
-- https://bit.ly/3skVSzo

-- ---------------------------------------------------------------------
-- § Librería auxiliares                                              --
-- ---------------------------------------------------------------------

import SintaxisSemantica
import Data.List

-- ---------------------------------------------------------------------
-- Equivalencia lógica                                                --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 1: Definir la función
--    esEquivalente :: Prop -> Prop -> Bool
-- tal que (esEquivalente f g) se verifica si f y g son
-- equivalentes. Por ejemplo,
--    esEquivalente (p <--> q) ((p --> q) /\ (q --> p))  ==  True
--    esEquivalente (p --> q)  ((no p) \/ q)             ==  True
--    esEquivalente (p /\ q)   (no ((no p) \/ (no q)))   ==  True
--    esEquivalente (p \/ q)   (no ((no p) /\ (no q)))   ==  True
-- ---------------------------------------------------------------------

esEquivalente :: Prop -> Prop -> Bool
esEquivalente f g =
  esValida (Equi f g)

-- ---------------------------------------------------------------------
-- § Transformación a forma normal negativa                           --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 2: Definir la función
--    eliminaEquivalencias :: Prop -> Prop
-- tal que (eliminaEquivalencias f) es una fórmula equivalente a f sin
-- signos de equivalencia. Por ejemplo,
--    eliminaEquivalencias (p <--> q)
--    == ((p --> q) /\ (q --> p))
--    eliminaEquivalencias ((p <--> q) /\ (q <--> r))
--    == (((p --> q) /\ (q --> p)) /\ ((q --> r) /\ (r --> q)))
-- ---------------------------------------------------------------------

eliminaEquivalencias :: Prop -> Prop
eliminaEquivalencias (Atom f)   =
  Atom f
eliminaEquivalencias (Neg f)    =
  Neg (eliminaEquivalencias f)
eliminaEquivalencias (Conj f g) =
  Conj (eliminaEquivalencias f) (eliminaEquivalencias g)
eliminaEquivalencias (Disj f g) =
  Disj (eliminaEquivalencias f) (eliminaEquivalencias g)
eliminaEquivalencias (Impl f g) =
  Impl (eliminaEquivalencias f) (eliminaEquivalencias g)
eliminaEquivalencias (Equi f g) =
  Conj (Impl (eliminaEquivalencias f) (eliminaEquivalencias g))
       (Impl (eliminaEquivalencias g) (eliminaEquivalencias f))

-- ---------------------------------------------------------------------
-- Ejercicio 3: Definir la función
--    eliminaImplicaciones :: Prop -> Prop
-- tal que (eliminaImplicaciones f) es una fórmula equivalente a f sin
-- signos de implicación. Por ejemplo,
--    eliminaImplicaciones (p --> q)
--    == (no p \/ q)
--    eliminaImplicaciones (eliminaEquivalencias (p <--> q))
--    == ((no p \/ q) /\ (no q \/ p))
--
-- Nota: Se supone que f no tiene signos de equivalencia.
-- ---------------------------------------------------------------------

eliminaImplicaciones :: Prop -> Prop
eliminaImplicaciones (Atom f)   =
  Atom f
eliminaImplicaciones (Neg f)    =
  Neg (eliminaImplicaciones f)
eliminaImplicaciones (Conj f g) =
  Conj (eliminaImplicaciones f) (eliminaImplicaciones g)
eliminaImplicaciones (Disj f g) =
  Disj (eliminaImplicaciones f) (eliminaImplicaciones g)
eliminaImplicaciones (Impl f g) =
  Disj (Neg (eliminaImplicaciones f)) (eliminaImplicaciones g)
eliminaImplicaciones _ = error "Imposible"

-- ---------------------------------------------------------------------
-- Ejercicio 4: Definir la función
--    interiorizaNegacion :: Prop -> Prop
-- tal que (interiorizaNegacion f) es una fórmula equivalente a f donde
-- las negaciones se aplican sólo a fórmulas atómicas. Por ejemplo,
--    interiorizaNegacion (no (no p))         ==  p
--    interiorizaNegacion (no (p /\ q))       ==  (no p \/ no q)
--    interiorizaNegacion (no (p \/ q))       ==  (no p /\ no q)
--    interiorizaNegacion (no (no (p \/ q)))  ==  (p \/ q)
--    interiorizaNegacion (no ((no p) \/ q))  ==  (p /\ no q)
--
-- Nota: Se supone que f no tiene equivalencias ni implicaciones.
-- ---------------------------------------------------------------------

interiorizaNegacion :: Prop -> Prop
interiorizaNegacion (Atom f)   =
  Atom f
interiorizaNegacion (Neg f)    =
  interiorizaNegacionAux f
interiorizaNegacion (Conj f g) =
  Conj (interiorizaNegacion f) (interiorizaNegacion g)
interiorizaNegacion (Disj f g) =
  Disj (interiorizaNegacion f) (interiorizaNegacion g)
interiorizaNegacion _ = error "Imposible"

interiorizaNegacionAux :: Prop -> Prop
interiorizaNegacionAux (Atom f)   =
  Neg (Atom f)
interiorizaNegacionAux (Neg f)    =
  interiorizaNegacion f
interiorizaNegacionAux (Conj f g) =
  Disj (interiorizaNegacionAux f) (interiorizaNegacionAux g)
interiorizaNegacionAux (Disj f g) =
  Conj (interiorizaNegacionAux f) (interiorizaNegacionAux g)
interiorizaNegacionAux _ = error "Imposible"

-- ---------------------------------------------------------------------
-- Ejercicio 5: Definir la función
--    formaNormalNegativa :: Prop -> Prop
-- tal que (formaNormalNegativa f) es una fórmula equivalente a f en
-- forma normal negativa. Por ejemplo,
--    formaNormalNegativa (p <--> q)
--    == ((no p \/ q) /\ (no q \/ p))
--    formaNormalNegativa ((p \/ (no q)) --> r)
--    == ((no p /\ q) \/ r)
--    formaNormalNegativa ((p /\ (q --> r)) --> s)
--    == ((no p \/ (q /\ no r)) \/ s)
-- ---------------------------------------------------------------------

formaNormalNegativa :: Prop -> Prop
formaNormalNegativa =
  interiorizaNegacion . eliminaImplicaciones . eliminaEquivalencias

-- ---------------------------------------------------------------------
-- Literales                                                          --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 6: Definir la función
--    literal :: Prop -> Bool
-- tal que (literal f) se verifica si la fórmula F es un literal. Por
-- ejemplo,
--    literal p               ==  True
--    literal (no p)          ==  True
--    literal (no (p --> q))  ==  False
-- ---------------------------------------------------------------------

literal :: Prop -> Bool
literal (Atom _)       = True
literal (Neg (Atom _)) = True
literal _              = False

-- ---------------------------------------------------------------------
-- Ejercicio 7: Definir el tipo de dato Literal como sinónimo de
-- fórmula.
-- ---------------------------------------------------------------------

type Literal = Prop

-- ---------------------------------------------------------------------
-- Ejercicio 8: Definir la función
--    complementario :: Literal -> Literal
-- tal que (complementario l) es el complementario de l. Por ejemplo,
--    complementario p       ==  no p
--    complementario (no p)  ==  p
-- ---------------------------------------------------------------------

complementario :: Literal -> Literal
complementario (Atom f)       = Neg (Atom f)
complementario (Neg (Atom f)) = Atom f
complementario _              = error "Imposible"

-- ---------------------------------------------------------------------
-- Ejercicio 9: Definir la función
--    literalesFormulaFNN :: Prop -> [Literal]
-- tal que (literalesFormulaFNN f) es el conjunto de los literales de la
-- fórmula en forma normal negativa f.
--    literalesFormulaFNN (p \/ ((no q) \/ r))  ==  [p,no q,r]
--    literalesFormulaFNN p                     ==  [p]
--    literalesFormulaFNN (no p)                ==  [no p]
-- ---------------------------------------------------------------------

literalesFormulaFNN :: Prop -> [Literal]
literalesFormulaFNN (Disj f g) =
  literalesFormulaFNN f `union` literalesFormulaFNN g
literalesFormulaFNN (Conj f g) =
  literalesFormulaFNN f `union` literalesFormulaFNN g
literalesFormulaFNN f          = [f]

-- ---------------------------------------------------------------------
-- Transformación a forma normal conjuntiva                           --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 10: Definir la función
--    interiorizaDisyuncion :: Prop -> Prop
-- tal que (interiorizaDisyuncion f) es una fórmula equivalente a f
-- donde las disyunciones sólo se aplica a disyunciones o literales. Por
-- ejemplo,
--    interiorizaDisyuncion (p \/ (q /\ r))  ==  ((p \/ q) /\ (p \/ r))
--    interiorizaDisyuncion ((p /\ q) \/ r)  ==  ((p \/ r) /\ (q \/ r))
-- Nota: Se supone que f está en forma normal negativa.
-- ---------------------------------------------------------------------

interiorizaDisyuncion :: Prop -> Prop
interiorizaDisyuncion (Disj (Conj f1 f2) g) =
  interiorizaDisyuncion
  (Conj (Disj (interiorizaDisyuncion f1) (interiorizaDisyuncion g))
        (Disj (interiorizaDisyuncion f2) (interiorizaDisyuncion g)))
interiorizaDisyuncion (Disj f (Conj g1 g2)) =
  interiorizaDisyuncion
  (Conj (Disj (interiorizaDisyuncion f) (interiorizaDisyuncion g1))
        (Disj (interiorizaDisyuncion f) (interiorizaDisyuncion g2)))
interiorizaDisyuncion (Conj f g) =
  Conj (interiorizaDisyuncion f) (interiorizaDisyuncion g)
interiorizaDisyuncion (Disj f g)
  | tieneConj (Disj f g) = interiorizaDisyuncion
                           (Disj (interiorizaDisyuncion f)
                                 (interiorizaDisyuncion g))
  | otherwise = Disj (interiorizaDisyuncion f)
                     (interiorizaDisyuncion g)
interiorizaDisyuncion f = f

tieneConj :: Prop -> Bool
tieneConj (Conj _ _) = True
tieneConj (Disj f g) = tieneConj f || tieneConj g
tieneConj _          = False

-- ---------------------------------------------------------------------
-- Ejercicio 11: Definir la función
--    formaNormalConjuntiva :: Prop -> Prop
-- tal que (formaNormalConjuntiva f) es una fórmula equivalente a f en
-- forma normal conjuntiva. Por ejemplo,
--    formaNormalConjuntiva (p /\ (q --> r))
--    == (p /\ (no q \/ r))
--    formaNormalConjuntiva (no (p /\ (q --> r)))
--    == ((no p \/ q) /\ (no p \/ no r))
--    formaNormalConjuntiva (no(p <--> r))
--    == (((p \/ r) /\ (p \/ no p)) /\ ((no r \/ r) /\ (no r \/ no p)))
-- ---------------------------------------------------------------------

formaNormalConjuntiva :: Prop -> Prop
formaNormalConjuntiva =
  interiorizaDisyuncion . formaNormalNegativa

-- ---------------------------------------------------------------------
-- Transformación a forma normal disyuntiva                           --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 12: Definir la función
--    interiorizaConjuncion :: Prop -> Prop
-- tal que (interiorizaConjuncion f) es una fórmula equivalente a f
-- donde las conjunciones sólo se aplica a conjunciones o literales. Por
-- ejemplo,
--    interiorizaConjuncion (p /\ (q \/ r))  ==  ((p /\ q) \/ (p /\ r))
--    interiorizaConjuncion ((p \/ q) /\ r)  ==  ((p /\ r) \/ (q /\ r))
-- Nota: Se supone que f está en forma normal negativa.
-- ---------------------------------------------------------------------

interiorizaConjuncion :: Prop -> Prop
interiorizaConjuncion (Conj (Disj f1 f2) g) =
  interiorizaConjuncion
  (Disj (Conj (interiorizaConjuncion f1) (interiorizaConjuncion g))
        (Conj (interiorizaConjuncion f2) (interiorizaConjuncion g)))
interiorizaConjuncion (Conj f (Disj g1 g2)) =
  interiorizaConjuncion
  (Disj (Conj (interiorizaConjuncion f) (interiorizaConjuncion g1))
        (Conj (interiorizaConjuncion f) (interiorizaConjuncion g2)))
interiorizaConjuncion (Disj f g) =
  Disj (interiorizaConjuncion f) (interiorizaConjuncion g)
interiorizaConjuncion f = f

-- ---------------------------------------------------------------------
-- Ejercicio 13: Definir la función
--    formaNormalDisyuntiva :: Prop -> Prop
-- tal que (formaNormalDisyuntiva f) es una fórmula equivalente a f en
-- forma normal disyuntiva. Por ejemplo,
--    formaNormalDisyuntiva (p /\ (q --> r))
--    == ((p /\ no q) \/ (p /\ r))
--    formaNormalDisyuntiva (no (p /\ (q --> r)))
--    == (no p \/ (q /\ no r))
-- ---------------------------------------------------------------------

formaNormalDisyuntiva :: Prop -> Prop
formaNormalDisyuntiva =
  interiorizaConjuncion . formaNormalNegativa
