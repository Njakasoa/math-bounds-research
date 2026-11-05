# Revue indépendante de l’erreur Euler–échantillonnage exact

5 novembre 2026. Paquet certified-euler-error-20261105, relu sans modification de ses sources ni scripts. Reconstruction sur copie fraîche ; journaux et comparaison des sources reproduits dans verification/.

## Verdict mathématique

Aucun défaut identifié dans les hypothèses, les indices ou les preuves lues. Les résultats comparent effectivement deux trajectoires utilisant la même entrée, maintenue constante sur chaque intervalle du maillage. Ils ne comparent pas Euler à une formule à entrée variable substituée abusivement dans une exponentielle à paramètres constants.

## Preuve locale

La borne 0≤exp(−z)−1+z≤z²/2 pour z≥0 est correcte. L’argument de monotonie utilisé dans Lean est valide : la dérivée de 1−z+z²/2−exp(−z) vaut z−1+exp(−z), non négative par l’inégalité de tangente de l’exponentielle. L’évaluation à zéro donne la majoration recherchée.

Le défaut local est exactement le produit de x−f(v) par ce reste exponentiel, au signe près. La condition x∈[0,1] et v≥0 donne |x−f(v)|≤1. Avec 0≤v≤M et τ≥0, le défaut est donc au plus τ²(1+M)²/2. Aucune restriction supérieure de pas n’est requise pour cette borne locale. C’est un défaut non divisé par le pas, contrairement à certaines conventions pour « erreur de troncature locale ».

## Propagation globale

Sous M≥0 et 0<τ≤1/(1+M), la pente Euler appartient à [0,1−τ]. Le facteur κ=1−τ est donc non négatif et strictement inférieur à 1. Cette condition est suffisante, plus restrictive que la seule admissibilité physique du jalon précédent ; le paquet ne doit pas la présenter comme nécessaire.

Le défaut local est évalué à l’état exact Y(n), dont l’appartenance à [0,1] est prouvée. L’état initial Euler X(0) peut être arbitraire pour la borne d’erreur ; seul Y(0) doit être physique. Pour garantir en plus les deux trajectoires dans [0,1], les deux conditions initiales physiques sont explicitement requises.

La récurrence e(n+1)≤(1−τ)e(n)+τ²(1+M)²/2 conduit exactement à

e(n)≤(1−τ)^n e(0)+τ(1+M)²[1−(1−τ)^n]/2.

La division par τ exige τ>0 et cette hypothèse est présente. À n=0 le terme forcé est nul. Le cas M=0,τ=1 donne κ=0 et reste valide, avec 0^0=1 au départ. À départ commun, la borne est uniforme sur tous les indices de grille, sans croissance avec l’horizon. Les unités physiques indiquées dans le rapport sont cohérentes après τ=k_off h et M=k_on L_max/k_off.

## Sauts et portée continue

Les deux récurrences utilisent v(n) sur le pas de nτ à (n+1)τ. Le segment suivant démarre à la valeur finale du précédent et utilise v(n+1). Les conditions initiales, les valeurs aux extrémités et les égalités de jonction sont formalisées.

La dérivée prouvée est celle de chaque segment prolongé avec son entrée constante. Ce n’est pas une dérivée globale de la trajectoire assemblée au point de saut : les dérivées à gauche et à droite peuvent différer. Le paquet ne définit pas et ne prouve pas l’unicité d’une fonction continue globale assemblée comme objet unique. Il établit les récurrences exactes et les interfaces de segments ; cette distinction a été signalée à l’auteur pour être rendue explicite au conditionnement final.

La borne porte seulement sur les instants de grille. Elle ne couvre ni un interpolant Euler entre ces instants, ni les sauts d’entrée non alignés, ni l’erreur introduite en remplaçant une entrée continûment variable par son maintien constant. Pas de validation biologique, d’optimalité ou de nouveauté scientifique.

## Audit indépendant des tests d’intervalles

Le script check_error.py a été exécuté sans modification dans la copie : 572 configurations locales et 15 trajectoires/cas limites passent. Les 12 trajectoires principales utilisent deux mêmes signaux sur six maillages, avec les mêmes commutations aux temps 1/4,1/2,3/4. Le calcul rationnel de la branche au début de chaque nouvelle maille prend bien la nouvelle entrée.

L’encadrement de exp(−z) par les sommes alternées de degrés 20 et 21 est mathématiquement valide pour 0≤z≤1 : les termes décroissent en valeur absolue, la somme impaire est inférieure et la somme paire supérieure. La propagation prend les quatre coins du rectangle état/exponentielle ; cette précaution traite correctement les deux signes possibles de x−f(v). Les assertions utilisent Fraction, pas des flottants.

L’algorithme d’encadrement Python n’est pas formalisé dans Lean. Ses tests restent distincts de la preuve universelle. Les cas M=0,τ=1, conditions initiales distinctes avec état Euler hors boîte et horizon nul sont présents.

À τ=1/4 et M=3, la borne finale sur l’horizon 1 est environ 1,367, donc peu informative puisque deux états physiques diffèrent d’au plus 1. À τ=1/128, cette borne est environ 0,03960, avec erreurs finales encadrées d’environ 0,0008495 pour l’entrée constante et 0,0020303 pour le signal commuté. Cela illustre le caractère conservateur annoncé, sans remplacer une preuve d’ordre ni garantir une tolérance donnée.

## Bibliographie revérifiée

Les trois pages citées ont été ouvertes directement pendant cette revue :

- [Driscoll et Braun, Euler’s method](https://fncbook.com/julia/euler/) : défaut local non normalisé d’ordre deux, convention LTE normalisée et propagation classique par récurrence. La borne générique croît avec l’horizon ; elle n’est pas présentée à tort comme la constante particulière du paquet.
- [Driscoll et Braun, Absolute stability](https://fncbook.com/python/absstab-diffusion/) : facteur Euler 1+hλ et stabilité au sens de suite bornée pour |1+hλ|≤1, distincte de la contraction stricte utilisée ici.
- [Documentation LLNL SUNDIALS](https://computing.llnl.gov/projects/sundials/usage-notes) : traitement adapté des discontinuités et distinction erreurs de modèle/résolution. Il s’agit d’une documentation d’implémentation, pas d’une preuve du résultat propre au paquet.

Les usages et limites bibliographiques du dossier concordent avec les passages lus.

## Reconstruction et contrôle des axiomes

Le rebuild.sh original est exécuté sur une copie sans objets locaux préexistants, avec son parallélisme inchangé. Le binaire Lean et le commit mathlib sont vérifiés ; le chemin d’import ne contient que le nouveau build et les dépendances mathlib. Le cache mathlib est réutilisé, pas entièrement recompilé.

Les 21 noms d’audit couvrent les 21 théorèmes/lemmes nouveaux, y compris les lemmes simp. La recherche de sorry/admit, axiomes ajoutés et contournements natifs est négative. Les empreintes et la comparaison des sources/scripts sont conservées dans verification/independent-source-comparison.json.

Le rebuild.sh original complet termine avec code 0 : sept modules reconstruits puis AuditEulerError exécuté. verify_outputs.py termine avec code 0, statut PASS pour les 21 noms. Les dépendances axiomatiques se limitent à propext, Classical.choice et Quot.sound. Aucun sorryAx. Les diagnostics restants sont uniquement des avertissements de style tactique. Les sources et scripts restent identiques au paquet gelé après reconstruction.

**Verdict final : accord sur le jalon et sur la comparaison Euler–échantillonnage exact sous ses hypothèses. Aucun blocage mathématique ou de compilation.** La précision sur les segments et les dérivées aux sauts doit être conservée dans le rapport final ; aucune modification des preuves n’est requise.
