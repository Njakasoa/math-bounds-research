# Relecture indépendante du jalon de suivi

5 novembre 2026. Paquet source : certified-tracking-bound-20261105. La reconstruction utilise une copie indépendante fraîche ; ses journaux sont reproduits dans verification/. Aucune source ni script du paquet modifié.

## Analyse mathématique

La borne annoncée est correcte pour la récurrence discrète déjà définie, avec u(n)∈[−1,1], x(0) réel arbitraire et |u(n+1)−u(n)|≤δ. Elle utilise la cible f(u)=1/(1+4u²), l’erreur e(n)=|x(n)−f(u(n))|, le taux κ=12/13, et une constante de Lipschitz globale commode 2 pour f.

La preuve de la constante 2 n’hypothèse pas un dénominateur non nul : sa stricte positivité est démontrée pour tous réels u et v. Le résultat n’est pas annoncé optimal, ce qui est exact.

L’indexation est correctement conservée : x(n+1) est calculé avec u(n), mais comparé à f(u(n+1)). La différence f(u(n+1))−f(u(n)) reste dans la majoration. On obtient e(n+1)≤κe(n)+2|u(n+1)−u(n)|.

La convolution comporte les indices j=0,…,n−1 et le poids κ^(n−1−j). Le terme le plus récent a donc le poids 1, et non κ. À n=0, la somme est vide ; à n=1, la contribution est 2|u(1)−u(0)| ; à n=2, elle vaut 2κ|u(1)−u(0)|+2|u(2)−u(1)|. Les soustractions naturelles dans les exposants sont maîtrisées par j<n dans la preuve de récurrence.

La somme géométrique donne exactement la borne finie e(n)≤κ^n e(0)+26δ(1−κ^n), puis la borne plus grossière κ^n e(0)+26δ. Le coefficient 26 vaut 2/(1−12/13). L’absence d’une hypothèse explicite δ≥0 dans la forme finie n’est pas une faille : la condition de variation l’implique déjà ; les lemmes de récurrence à contribution signée restent également valides avec κ≥0. La version uniforme générale impose ou déduit la non-négativité au moment où elle est nécessaire.

Les hypothèses des lemmes abstraits sont explicites : contraction de chaque application, point fixe instantané, récurrence de la trajectoire et borne de dérive si utilisée. Les lemmes de convolution n’exigent pas κ<1 ; ce dernier est nécessaire aux formes uniformes contractantes, et y est présent. La somme géométrique polynomiale couvre aussi κ=1 sans division par zéro ; les formules divisées exigent κ<1.

## Portée

Le suivi est une majoration d’erreur, pas un suivi exact de la cible. Une variation bornée non nulle ne force pas l’erreur à converger vers zéro. Le cycle alterné précédent reste compatible avec la borne, qui y est très grossière. Aucune conclusion de temps continu ou de nouveauté scientifique.

L’état initial peut être hors de [−5,5] : la contraction affine en l’état est globale. L’invariance de cette boîte, distincte, exige toujours d’y commencer. Les preuves de suivi n’ajoutent pas furtivement cette condition.

Les constantes 2, 12/13 et 26 sont conservatrices et ne constituent pas une optimisation du suivi. Le jalon formalise les estimations finies, pas un théorème supplémentaire de limite supérieure asymptotique ou un algorithme de synthèse.

## Expériences

Le script original experiments/check_tracking.py a été exécuté dans la copie. Les quatre cas passent en arithmétique Fraction exacte : entrée constante, rampe, cycle alterné et entrée non monotone. Sur la rampe de 50 mises à jour, l’erreur maximale calculée est environ 0,02697705 pour une borne forcée uniforme 0,26, conformément au rapport. Les décimales sont seulement une présentation.

Un contrôle complémentaire utilise l’état initial x(0)=100, hors de la boîte, avec la même rampe ; toutes les assertions de suivi passent. Le cas d’horizon nul a également été exécuté ; son contenu mathématique e(0)≤e(0) est contrôlé directement dans la preuve. Ces exemples ne remplacent pas les théorèmes universels.

## Reproduction et audits

Le rebuild.sh original est exécuté intégralement, avec son parallélisme -j2 inchangé, dans une copie fraîche sans objets .olean ni répertoire build initial. Le script vérifie l’empreinte du binaire Lean 4.34.1 et le commit mathlib, retire l’ancien LEAN_PATH et utilise seulement le nouveau build plus mathlib/dépendances. Les objets mathlib sont réutilisés : ce n’est pas une reconstruction intégrale de mathlib ni un audit du compilateur.

Le script verify_outputs.py vérifie la présence et les axiomes de 21 déclarations nommées. Cette liste n’est pas exhaustive : le petit lemme convolution_zero est une 22e déclaration. Il fait l’objet d’un audit indépendant séparé pour préserver le paquet gelé. La recherche des marqueurs sorry/admit, d’axiomes ajoutés et de contournements natifs dans les sources est négative.

Les empreintes et l’identité des sources/scripts avec le paquet gelé sont enregistrées dans verification/independent-source-comparison.json. SHA256SUMS, annoncé dans le README, n’était pas encore présent lors de la copie : l’auteur indique qu’il sera généré lors du conditionnement final après intégration des rapports. Ce point ne bloque pas la reconstruction ni la comparaison indépendante des sources.

Le résultat final des compilations et audits est consigné ci-dessous.

## Résultat final

Le rebuild.sh original complet termine avec code 0 : sept modules reconstruits, puis AuditTracking exécuté. verify_outputs.py termine avec code 0 et statut PASS pour ses 21 noms. L’audit complémentaire de convolution_zero termine lui aussi avec code 0. Les 22 théorèmes/lemmes nouveaux sont ainsi couverts ; tous ne dépendent que de propext, Classical.choice et Quot.sound. Aucun sorryAx ni nouvel axiome. Les cinq avertissements restants concernent uniquement le style de séquencement des tactiques.

Les quatre expériences originales et les contrôles complémentaires passent. La comparaison finale des sources et scripts avec le paquet gelé est identique à celle initiale. Aucun blocage mathématique ou de compilation ne subsiste.

**Verdict : accord sur le jalon et sur la borne de suivi, sous les hypothèses explicites et avec les limites du rapport.** Le conditionnement final doit seulement clarifier les 21 audits nommés plus le complément indépendant, et générer son manifeste SHA256SUMS. Cela ne requiert aucune modification des preuves.
