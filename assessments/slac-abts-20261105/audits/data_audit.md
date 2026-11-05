# Audit descriptif indépendant : SLAC / ABTS, archive 25 °C

Date : 5 novembre 2026. **Aucun ajustement, aucune simulation, aucune validation biologique et aucune modification des données sources.** Les valeurs numériques ci-dessous conservent les unités **nommées** par EnzymeML ; la divergence avec les définitions SBML littérales doit être résolue avant toute interprétation physique automatique.

## Résultat et limites immédiates

- Archive ZIP valide, **22 membres**, dont **8 CSV sans en-tête** ; empreinte SHA256 vérifiée avant et après audit : `6404d43ced75108a126f1f071057b8600e4aeecefb720c53dc29607bc774afa3`.
- **8 conditions × 3 trajectoires de réplicats × 11 instants = 264 concentrations**. Les 352 cellules numériques incluent aussi 88 temps. Une seule espèce observée : **s1 = ABTS**, concentration nommée « umole / l » (µM), et non le produit oxydé. Aucun réplicat complet dupliqué.
- **0 cellule manquante, 0 valeur non finie, 0 concentration négative ou nulle, 0 instant dupliqué dans un CSV.** Les 8 grilles temporelles sont identiques, strictement croissantes et non uniformes.
- Les 8 moyennes mesurées à t = 0 sont inférieures aux concentrations initiales nominales. **23 des 24 valeurs individuelles** le sont également. Ne pas remplacer les valeurs nominales par les mesures, ni l'inverse, sans décision explicite.
- Un décalage persistant de C6 et une petite augmentation temporelle de B3 sont à examiner ; ils ne constituent pas des erreurs démontrées et **aucune exclusion n'est appliquée**.
- **Blocage d'interprétation des unités : cinq définitions sur six présentent un facteur dix incompatible avec leur nom.** Une lecture générique du SBML et une lecture fondée sur les noms EnzymeML ne sont donc pas équivalentes.

## Schéma et conditions

Source : `experiment.xml`, espace de noms SBML `http://www.sbml.org/sbml/level3/version2/core`, espace de noms EnzymeML `http://sbml.org/enzymeml/version2`.

La jointure est `measurement/@file → files/file/@id → @file et @format → formats/format/@id`. Ne pas traiter la première ligne de chaque CSV comme un en-tête.

| Colonne, base zéro | Type XML | Espèce | Unité XML | Contenu |
|---|---|---|---|---|
| 0 | time | aucune | u2, nom min | temps |
| 1 | conc | s1, ABTS | u4, nom umole / l | réplicat A2 à A9 |
| 2 | conc | s1, ABTS | u4, nom umole / l | réplicat B2 à B9 |
| 3 | conc | s1, ABTS | u4, nom umole / l | réplicat C2 à C9 |

Les 24 colonnes de concentration portent `isCalculated="False"`. Ce champ ne démontre pas l'absence de calibration ou de transformation préalable : cette archive contient des concentrations, pas des absorbances brutes.

Conditions communes déclarées : température 298,15, unité nommée K, soit **25 °C selon le nom** ; pH 3 ; volume 200 µL ; enzyme active p0 nominale 0,073938727 µM ; acétate s0 nominal 50 mM ; produit s2 nominal 0 µM. Les conditions initiales de p1 (enzyme inactive), s3 (oxygène) et s4 (eau) ne sont pas renseignées dans les annotations `initConc`. Aucun relevé de ces espèces n'est présent ; ne pas inventer une mesure ou une condition initiale manquante.

### Concentrations nominales et premier point mesuré

Toutes les concentrations sont en µM **selon le nom d'unité**, sans correction du SBML. L'écart-type est l'écart-type empirique entre les trois réplicats, dénominateur n−1 = 2 ; il ne s'agit ni d'un SEM ni d'une borne d'erreur.

| Condition / fichier | Réplicats | Nominal | Moyenne t0 | Écart-type t0 | Écart moyen au nominal | Moyenne au dernier temps |
|---|---|---:|---:|---:|---:|---:|
| m0 / data/m0.csv | A2,B2,C2 | 5 | 3,933968 | 0,134669 | −21,3206 % | 2,097257 |
| m1 / data/m1.csv | A3,B3,C3 | 10 | 8,309342 | 0,090031 | −16,9066 % | 4,812316 |
| m2 / data/m2.csv | A4,B4,C4 | 15 | 13,113888 | 0,274898 | −12,5741 % | 8,422090 |
| m3 / data/m3.csv | A5,B5,C5 | 25 | 22,255619 | 0,104846 | −10,9775 % | 15,516161 |
| m4 / data/m4.csv | A6,B6,C6 | 50 | 48,429665 | 3,175008 | −3,1407 % | 37,731276 |
| m5 / data/m5.csv | A7,B7,C7 | 75 | 72,243264 | 0,187828 | −3,6756 % | 59,788179 |
| m6 / data/m6.csv | A8,B8,C8 | 100 | 97,806286 | 0,604339 | −2,1937 % | 83,618145 |
| m7 / data/m7.csv | A9,B9,C9 | 150 | 145,886298 | 1,008382 | −2,7425 % | 130,272433 |

Valeurs exactes, minima/maxima et statistiques aux 88 couples condition/instant : `data_audit.json`, `condition_summary.csv`, `pointwise_replicate_summary.csv`. Les données sources ne sont pas réécrites.

## Temps, valeurs et signalements descriptifs

Grille commune, en minutes **selon le nom d'unité** :

`0 ; 1,4666666666666668 ; 2,9166666666666665 ; 4,366666666666666 ; 5,833333333333333 ; 7,483333333333333 ; 8,983333333333333 ; 10,483333333333333 ; 11,983333333333333 ; 13,483333333333333 ; 14,983333333333333`.

Les pas vont de 1,45 à 1,65, avec médiane 1,5. La concentration minimale du fichier est 2,0390637371819036, la maximale 146,63916781389747.

**C6, condition m4 :** C6 dépasse A6 et B6 aux 11 instants. La différence à la moyenne de A6/B6 varie de **3,982572 à 5,496495 µM nommés**, alors que l'écart absolu maximal entre A6 et B6 est **0,201856**. À t0 : A6 = 46,698428082475004 ; B6 = 46,496571683650686 ; C6 = 52,09399506726548, pour un nominal de 50. Le CV empirique de m4 varie de 5,6869 % à 6,5559 %. Ce profil peut motiver une revue de la provenance/calibration ; trois réplicats et un décalage persistant ne permettent pas d'identifier à eux seuls une cause ou un point à supprimer.

**B3, condition m1 :** une seule augmentation parmi 240 incréments intra-trajectoire : de 5,3451442152233914 à 5,399699998689423 entre t = 10,483333333333333 et 11,983333333333333, soit **+0,0545557834660313 µM nommés**. Les 239 autres incréments sont négatifs. Le modèle supposant une consommation monotone n'implique pas que toute fluctuation positive d'une observation soit erronée.

Aucun test formel de valeur aberrante n'est appliqué, et aucun seuil d'exclusion n'est inventé.

## Divergence des unités SBML : conserver et résoudre explicitement

En SBML, chaque composante représente `(multiplier × 10^scale × unité de base)^exponent`. L'archive utilise `scale="1"` sur plusieurs composantes qui seraient normalement à l'échelle zéro pour correspondre au nom. Les nombres suivants décrivent **l'encodage existant**, pas une correction proposée :

| ID | Nom dans l'archive | Sens littéral de la définition | Facteur littéral / unité nommée |
|---|---|---|---:|
| u0 | ul | 10⁻⁶ L | 1 |
| u1 | mM | 10⁻⁴ mol/L | 0,1 |
| u2 | min | 600 secondes | 10 |
| u3 | K | 10 kelvins | 10 |
| u4 | umole / l | 10⁻⁷ mol/L | 0,1 |
| u5 | 1 / min | 1/600 seconde⁻¹ | 0,1 |

Exemples : u2 porte `kind="second" exponent="1" scale="1" multiplier="60"`. u4 combine `litre exponent="-1" scale="1" multiplier="1"` et `mole exponent="1" scale="-6" multiplier="1"`. Une interprétation littérale ferait notamment de 298,15 u3 une température de 2981,5 K. Le nom et l'historique EnzymeML appuient l'intention usuelle, mais ne justifient pas une réparation silencieuse de l'archive.

L'audit conserve donc les valeurs et les deux interprétations. Une simulation ou certification ultérieure doit annoncer son choix d'unités, préserver l'original et résoudre cette divergence au niveau de l'import.

## Incertitudes et limites d'observation

- Trois trajectoires de puits par condition ne prouvent pas trois préparations biologiques indépendantes. Les instants d'un même puits ne sont pas des réplicats indépendants ; une calibration commune peut aussi corréler les puits.
- Aucun champ d'erreur par observation, variance, covariance, limite de détection, censure ou incertitude de calibration n'est inclus dans les CSV. Les écarts-types empiriques n'imposent aucune borne absolue et leur estimation avec n = 3 reste fragile.
- Les absorbances brutes et données de calibration sont annoncées ailleurs dans le dépôt par le rapport de provenance, mais **ne figurent pas dans cette archive**. La transformation observationnelle complète n'est pas reconstructible avec ces seuls fichiers.
- Les trois champs `stdev` des paramètres sont distincts de l'erreur de mesure : k_cat = 23,8113065508133, stdev = 2,0801729247130765 ; K_M = 22,9403691771082, stdev = 2,4149800297892927 ; k_ie = 0,0608219180888591, stdev = 0,0008967639596557227. L'archive ne suffit pas à établir leur interprétation probabiliste. Les bornes d'optimisation ne sont pas des intervalles de confiance.
- Aucun signal de conformation ni trajectoire indépendante d'enzyme active/inactive ou de produit oxydé n'est mesuré ici. L'audit ne valide ni un mécanisme unique ni une intervention biologique.

## Sources et reproductibilité

1. Archive inspectée en lecture seule : `slac25.omex (original externe)`, notamment `experiment.xml`, `data/m0.csv` à `data/m7.csv`, `manifest.xml`, `history.log` et RDF.
2. Rapport fourni : `relevé de provenance initial fourni, résumé dans INPUTS.md` ; provenance externe reprise de ce rapport, non revérifiée sur le Web dans cet audit.
3. Dépôt : Max Häussler, DaRUS-3867, version 1, publication 9 janvier 2024, https://doi.org/10.18419/DARUS-3867 ; fichier https://doi.org/10.18419/DARUS-3867/12. Licence CC BY 4.0 selon le rapport fourni ; aucune licence embarquée dans cette archive.
4. Documentation annoncée par le rapport : https://github.com/EnzymeML/slac_modeling et https://raw.githubusercontent.com/EnzymeML/slac_modeling/main/slac_kinetics.ipynb. Aucun notebook exécuté.

Reproduction : `python audit_data.py`. Le script Python standard lit directement l'archive ZIP, utilise les espaces de noms explicites, vérifie les dimensions et préserve toutes les valeurs. Il régénère le JSON et les deux tableaux dérivés, pas ce rapport rédigé. L'empreinte originale a été revérifiée après analyse.
