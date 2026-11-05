# Audit indépendant du modèle SLAC 25 °C

Audit du 5 novembre 2026. Objet : sémantique mathématique, import, unités et incertitudes. Aucune expérience, intervention biologique, optimisation d'organisme ou validation conformationnelle. Notebook et données lus seulement ; aucun code téléchargé exécuté. Le petit script d'audit est une nouvelle implémentation indépendante.

## Conclusion utilisable

Le benchmark est exploitable **comme modèle de concentrations explicitement reconstruit**, pas comme simulation SBML générique fidèle sans avertissement. Deux erreurs d'import majeures sont documentées : les lois stockées sont déjà des dérivées négatives et plusieurs unités SBML ont un facteur 10 incompatible avec leur nom. La comparaison avec les courbes archivées du notebook appuie fortement l'interprétation en minutes et micromoles/litre.

Les champs `stdev` ne sont ni des bornes certaines ni une distribution jointe documentée. Les bornes sont des contraintes d'optimisation. Une boîte choisie à partir de ces valeurs peut servir à un **certificat conditionnel**, mais pas à annoncer une couverture expérimentale ou statistique garantie.

## 1. Provenance et fichiers

- Archive : `slac25.omex (original externe)`, SHA256 `6404d43ced75108a126f1f071057b8600e4aeecefb720c53dc29607bc774afa3`.
- Source du jeu : https://doi.org/10.18419/DARUS-3867 ; archive ciblée https://doi.org/10.18419/DARUS-3867/12. Les références/licence CC BY 4.0 proviennent du rapport de sélection fourni, non d'une nouvelle vérification de la licence ici.
- Notebook public : https://raw.githubusercontent.com/EnzymeML/slac_modeling/main/slac_kinetics.ipynb, copie `slac_kinetics.readonly.ipynb`, SHA256 `14d2c07bfc6b07e10e3317bd3176f7b8b1479c0ebe015732b54627235c79e9a8`. Il s'agit de `main` récupéré le jour de l'audit ; l'empreinte fige cette copie.
- Extraction vérifiable : `model_audit_extraction.json`, `extract_model_audit.py`. Les séquences biologiques ne sont pas dupliquées dans l'extraction ciblée.
- Courbes sans recalcul : `notebook_25C_saved_MM_curves.json`, cellule 28, sortie 0, traces 32–39, indices tous 0-based. Les temps et ordonnées sont conservés tels quels.

## 2. Ce que l'archive établit

Le modèle SBML L3V2 porte seulement l'attribut `name="SLAC kinetic assay"`. Aucun `timeUnits`, `extentUnits` ou `substanceUnits` global n'est fixé. Le volume du compartiment constant est 200 µL.

Espèces :

| ID | Fonction | constant | boundaryCondition | Initialisation dans SBML core |
|---|---|---:|---:|---|
| s0 | Acétate, absent des lois | true | false | 50, substanceUnits=u1 |
| s1 | Substrat ABTS observé | false | false | non renseignée |
| s2 | Produit ABTS oxydé | false | false | non renseignée |
| p0 | Enzyme active | false | false | non renseignée |
| p1 | Enzyme inactive | false | false | non renseignée |
| s3 | Oxygène, absent des réactions exportées | false | false | non renseignée |
| s4 | Eau, absente des réactions exportées | false | false | non renseignée |

Toutes les espèces ont `hasOnlySubstanceUnits=false`. Les conditions d'expérience sont dans les annotations EnzymeML, pas sous forme de scénarios SBML core : E0=0.073938727 µM, substrat nominal 5, 10, 15, 25, 50, 75, 100, 150 µM, produit initial 0, tampon 50 mM, température nommée 298.15 K, pH 3. Aucun p1 initial n'y est donné. Inactive=0 est une convention supplémentaire si on reconstruit cet état non observé.

Réactions exportées :

- r0 : s1 → s2, coefficients 1 ; modificateur p0 ; `reversible=false`. MathML = `-(s1*p0*k_cat)/(K_M+s1)`.
- r1 : p0 → p1, coefficients 1 ; p0 également déclaré modificateur ; `reversible=false`. MathML = `-k_ie*p0`.
- Les références stœchiométriques portent `constant=false`, mais aucune règle/événement les modifiant n'est présent.

**Piège de signe :** en SBML standard, un flux r0 négatif avec s1 réactant ferait croître s1, et le flux r1 négatif ferait croître p0. Ce n'est pas l'interprétation du notebook. En outre un flux SBML est une quantité par temps alors que les expressions visées sont des concentrations par temps : la gestion du volume doit être explicite. Les unités de substance manquent sur les espèces dynamiques ; s0 utilise une unité de concentration comme `substanceUnits`. L'archive ne doit donc pas être annoncée comme un modèle autonome directement simulable, ni silencieusement « corrigée ». Aucun validateur libSBML n'était installé et aucune validation formelle de schéma n'a été revendiquée.

### Unités : noms versus définition littérale

SBML compose chaque unité selon `(multiplier × 10^scale × kind)^exponent` ([documentation libSBML](https://sbml.org/software/libsbml/5.18.0/docs/formatted/python-api/classlibsbml_1_1_unit.html)).

| ID | Nom | Définition effective |
|---|---|---|
| u0 | ul | 10^-6 litre, cohérent |
| u1 | mM | 10^-4 mole/litre = 0.1 mM |
| u2 | min | 600 secondes = 10 minutes |
| u3 | K | 10 kelvins |
| u4 | umole / l | 10^-7 mole/litre = 0.1 µM |
| u5 | 1 / min | 1/600 seconde^-1 = 0.1 minute^-1 |

La colonne temps référence u2 ; cela ne fixe pas le temps du modèle SBML global absent. Le nom « min » et le notebook justifient la convention de travail minute, **pas** une assertion que le XML littéral encode correctement 60 s. Les valeurs CSV sont 0 à 14.983333333333333 ; sous la convention minute, les instants correspondent à 0,88,175,262,350,449,539,629,719,809,899 secondes, à l'arrondi décimal près. Les chaînes originales sont conservées dans le JSON.

### Paramètres exacts archivés

| Paramètre | Valeur | stdev | InitialValue | LowerBound | UpperBound | Unité visée |
|---|---:|---:|---:|---:|---:|---|
| k_cat | 23.8113065508133 | 2.0801729247130765 | 29.128355736210448 | 2.9128355736210447 | 291.2835573621045 | min^-1 |
| K_M | 22.9403691771082 | 2.4149800297892927 | 75.0 | 0.75 | 375.0 | µM |
| k_ie | 0.0608219180888591 | 0.0008967639596557227 | 0.011552453009332421 | 0.0002310490601866484 | 0.5776226504666211 | min^-1 |

Le XML nomme le champ `stdev`, pas `standarddeviation`. Il ne contient ni méthode de calcul, covariance/corrélations complètes, nombre de degrés de liberté, définition du bruit, pondération des résidus, bootstrap, ni intervalle de confiance.

### Observations

Huit CSV, 11 temps et trois réplicats A/B/C chacun : 264 concentrations. Toutes les colonnes observées ciblent s1 (`type=conc`, u4). Aucune mesure de produit, d'enzyme active/inactive ou d'oxygène. `isCalculated=False` est stocké, mais ne prouve pas que les nombres soient des mesures directes non transformées.

Les concentrations t0 diffèrent des concentrations nominales. Par exemple m0 : 4.046716568731849, 3.7848488080948997, 3.9703384718794066, pour 5 µM nominal ; m4 : 46.698428082475004, 46.496571683650686, 52.09399506726548, pour 50 µM nominal. Ne jamais remplacer l'un par l'autre implicitement. Les réplicats d'une même plaque ne garantissent pas indépendance de leurs erreurs de calibration.

## 3. Ce qu'ajoute le notebook (non exécuté)

Cellules 3/7/9/11 : minutes, conditions nominales, soustraction des blancs, conversion du signal 340 nm en ABTS par calibration linéaire ; cellule 13 : exclusion de 200 µM. Les CSV sont donc déjà calibrés, malgré `isCalculated=False`. L'OMEX ne contient ni absorbances brutes ni coefficients/covariance de calibration. La sortie 25 °C donne R²=0.9965 et RMSD=0.0525 en signal ; aucune propagation complète n'est établie.

Cellules 23/27/38 : k_cat et K_M proviennent d'un ajustement limité aux trois premières minutes, puis sont fixés pour l'ajustement ultérieur ; export explicite de « michaelis menten with enzyme inactivation ». Ce choix n'est pas le minimum AIC à 25 °C (-398, contre -514 pour inhibition compétitive + inactivation).

Cellule 28 : les huit courbes sauvegardées commencent à la moyenne des trois t0, non au nominal. Cela établit la visualisation, pas la fonction de coût. La signification exacte de `stdev` reste inconnue : le pourcentage de k_cat change entre étapes, empêchant d'affirmer un simple report de l'erreur initiale.

## 4. Modèle reconstruit et contrôle indépendant

Convention explicitement adoptée : S=s1 et E=p0 en µM ; t en minutes ; paramètres numériques ci-dessus.

    S' = -k_cat E S / (K_M + S)
    E' = -k_ie E
    observation = S

Les compléments P'= -S' et I'= -E' conservent S+P et E+I, si l'on choisit de reconstruire ces états non observés. Aucune dynamique d'O2/H2O n'est identifiable dans ce système exporté. Il ne contient ni complexe enzyme-substrat explicite ni état conformationnel : un ancien modèle de liaison ne peut lui être substitué.

Pour E0≥0, S0>0, k_cat≥0, K_M>0, k_ie≥0 :

    E(t)=E0 exp(-k_ie t)
    U(t)=k_cat E0 (1-exp(-k_ie t))/k_ie
    S0-S(t)+K_M log(S0/S(t))=U(t)

À k_ie=0, utiliser U=k_cat E0 t. La fonction de gauche est strictement décroissante en S>0, vaut 0 à S0 et tend vers +∞ quand S→0 : elle définit une unique solution 0<S≤S0. Les paramètres archivés satisfont ces conditions.

Contrôle numérique indépendant : les 800 points des huit courbes de la cellule 28 ont été comparés à cette racine implicite, avec les paramètres archivés et la moyenne t0 des réplicats. Écart maximal absolu : **1.9551503172010598×10^-7 µM**. Le calcul utilise `scipy.optimize.brentq` et la forme stable `-expm1(-k_ie*t)` ; c'est une concordance numérique, pas un certificat d'arrondi dirigé. Cela reproduit la visualisation sauvegardée, **pas** l'estimation, ses poids/résidus ou ses incertitudes.

## 5. Test de certificat réellement adapté

Proposition indépendante, non attribuée aux auteurs : pour une boîte annoncée à l'avance, construire une enveloppe de S(t) par monotonie et encadrement certifié de la racine.

- S(t) croît avec S0, K_M et k_ie ; décroît avec k_cat et E0, pour t≥0.
- Borne inférieure : S0_min, K_M_min, k_ie_min, k_cat_max, E0_max.
- Borne supérieure : S0_max, K_M_max, k_ie_max, k_cat_min, E0_min.
- Justification : U décroît avec k_ie ; la fonction implicite est strictement décroissante en S. Les dérivées implicites donnent les autres signes.
- Encadrer exp/log avec arithmétique d'intervalles dirigés ou restes de séries prouvés, puis vérifier des changements de signe à des extrémités rationnelles. Une simple racine flottante ou un échantillonnage de la boîte ne certifie rien.
- Tester aussi t=0, E0=0, k_cat=0 et la limite k_ie=0. Vérifier positivité du dénominateur K_M+S. Garder un mode d'abstention si les hypothèses ne sont pas satisfaites.

Utiliser les bornes d'optimisation comme boîte donne une garantie mathématique **conditionnelle à cette boîte**, pas une plausibilité statistique. Une boîte ±stdev ou ±2stdev est un scénario de sensibilité arbitraire tant que la calibration, la covariance, les étapes d'estimation et le bruit ne sont pas réétablis. Une concentration initiale prise comme exactement égale à t0 ou à sa moyenne est également une hypothèse, et l'erreur en t0 n'est alors pas une validation hors échantillon.

## 6. Blocage exact et limites

Lecture demandée : source d'implémentation EnzymePynetics épinglée par `requirements.txt`, https://github.com/FAIRChemistry/EnzymePynetics/tree/9557beb2da1f9116d08eb0ee996862894a8a37e7/EnzymePynetics/core. Résultat du moteur web : **denied, “Failed to fetch restricted URL”**. Aucun autre accès, contournement ou réessai de cette cible. Un premier lien sous l'organisation EnzymeML avait simplement donné 404 ; il n'établissait pas une source correcte.

Terminé indépendamment : inspection XML/CSV, copie/lecture du notebook public, extraction des courbes, vérification numérique d'une solution implicite, proposition de certificat. Non établi : exact algorithme de stdev, fonction de coût et pondérations, initialisation interne de l'ajustement, propagation de calibration, couverture statistique, adéquation unique du mécanisme ou validation biologique. La réussite du test proposé ne prouverait que la propriété mathématique annoncée pour le modèle reconstruit et les hypothèses choisies.
