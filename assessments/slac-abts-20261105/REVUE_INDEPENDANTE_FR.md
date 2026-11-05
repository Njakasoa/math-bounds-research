# Revue indépendante computationnelle SLAC/ABTS

5 novembre 2026. Relecture des fichiers de math-bounds-lab/slac-benchmark, sans modification de leurs sources. Aucun notebook téléchargé exécuté, aucune manipulation physique, aucune réestimation de paramètres ni recommandation expérimentale.

## Conclusion
Les courbes sauvegardées sont reproduites par le modèle de concentrations déclaré dans le notebook, avec les unités nommées minute/µM et l'initialisation par moyenne mesurée à t0. Cette concordance n'est pas une validation du SBML littéral, de l'estimation statistique ni du mécanisme biologique. L'obstruction à une contraction stricte globale du flot ou d'Euler sur un domaine contenant plusieurs points (S,0) est exacte.

## Sources et reproduction
Archive lue directement : slac25.omex (original externe).
SHA256 : 6404d43ced75108a126f1f071057b8600e4aeecefb720c53dc29607bc774afa3.
Notebook lu comme JSON : slac_kinetics.readonly.ipynb ; cellule28, première sortie Plotly, huit traces « michaelis menten with enzyme inactivation » de100 points. Cellules23,27,38 inspectées pour déclarations et export ; aucun code source du notebook exécuté.

Copies des scripts replay_declared_model.py et extract_model_audit.py exécutées dans une copie indépendante de contrôle. Leurs résultats reproduisent les valeurs annoncées : maximum racine implicite/courbes sauvegardées 1,9551503172010598×10^-7 µM ; maximum DOP853/racine implicite 3,2380143011323526×10^-10 µM.

Contrôle numérique supplémentaire écrit indépendamment : independent_replay.py, dans ce même dossier. Intégration scalaire Radau avec enzyme analytique, appariement des traces par leur moyenne initiale plutôt que par leur ordre. Résultat PASS pour8×100 points ; écart maximal sauvegardé≈1,955178206×10^-7 µM ; résidu maximal de l'identité intégrée≈5,48×10^-11 µM ; RMSE sur les240 observations après t0≈0,879737557720797 µM. Résultats complets : independent-results.json. Ce sont des contrôles flottants, sans arrondi dirigé ni preuve Lean.

## Conventions de signe et d'unités
Le MathML encode r0=−s1*p0*kcat/(KM+s1), tandis que s1 est réactant ; r1=−kie*p0 tandis que p0 est réactant. Un flux SBML négatif appliqué avec cette stœchiométrie fait croître les réactants. Le notebook déclare au contraire directement les dérivées négatives du substrat et du catalyseur. Cette différence ne peut pas être réparée silencieusement. Un flux SBML est une quantité par temps ; la conversion en dérivée de concentration doit également gérer le volume. Les unités globales de temps/substance/extent et certaines initialisations du core sont absentes.

Les définitions XML donnent u2=600secondes, u3=10kelvins, u4=10^-7mol/L, u1=10^-4mol/L et u5=1/600s^-1 ; elles diffèrent de leur nom par un facteur10. u0=10^-6L est cohérent. Les noms et le notebook appuient l'intention minute/µM, mais ne rendent pas l'encodage littéral correct. L'observation porte sur s1, pas sur le produit oxydé. La moyenne initiale correspond aux courbes sauvegardées, pas nécessairement à l'initialisation interne du coût d'ajustement.

## Identité analytique et hypothèses
Sous S0>0, E0≥0, kcat≥0, KM>0, d=kie≥0 et t≥0 :
E(t)=E0 exp(−dt),
U(t)=kcat E0∫₀ᵗ exp(−dr)dr,
S0−S(t)+KM log(S0/S(t))=U(t).
Pour d=0, U=kcat E0t ; pour d>0, U=kcat E0(1−exp(−dt))/d.
La fonction de S à gauche est strictement décroissante sur S>0, tend vers+∞ à zéro et vaut0 en S0. Elle définit donc une unique solution physique dans(0,S0]. La séparation de variables donne bien S′=−kcat E(t)S/(KM+S). Les limites E0=0 et kcat=0 donnent S constant.

La monotonie proposée pour une future enveloppe est correcte : S croît avec S0, KM et kie, décroît avec kcat et E0. Une boîte de paramètres indépendants donne une enveloppe conditionnelle même si elle ignore des corrélations, mais pas une couverture probabiliste. Aucun certificat d'intervalles de ce type n'a été produit par la reproduction flottante présente.

## Obstruction exacte de contraction
Pour le système autonome de deux états, chaque (S,0) est un équilibre. Le flot Φt et la transition Euler Gh fixent donc ces états. Si le domaine contient deux valeurs distinctes S1 et S2 à E=0, leur distance est strictement positive et inchangée :
d(Φt(S1,0),Φt(S2,0))=d((S1,0),(S2,0)).
Une inégalité de contraction uniforme avec κ<1 serait contradictoire. Même argument pour Gh, dans toute véritable métrique. Cela concerne les transitions, pas le champ de vecteurs lui-même considéré comme application.

## Réduction scalaire, portée finie
Avec la même enzyme prescrite E(t)=E0 exp(−dt), E0>0, kcat>0, KM>0, et0≤S≤Smax sur0≤t≤T fini :
a(t,S)=kcat E(t)KM/(KM+S)^2,
a_min=kcat E0 exp(−dT)KM/(KM+Smax)^2>0,
a_max=kcat E0/KM.
Pour0<h≤1/a_max, la transition scalaire S↦S−h kcat E(t)S/(KM+S) préserve[0,Smax] et sa dérivée est dans[0,1−h a_min]. La contraction est donc conditionnelle et finie dans le temps, avec la même entrée E(t) dans les trajectoires comparées. Ce n'est pas une contraction du couple(S,E) ni automatiquement le schéma Euler simultané sur les deux équations.

Pour les valeurs exportées et T≈14,9833min, Smax=150µM : a_min≈0,000542855min^-1, a_max≈0,0767458min^-1 ; à h=0,1min, κ≈0,9999457145. Le facteur proche de1 signale une borne faible, pas une forte robustesse expérimentale. Lorsque d>0, a_min tend vers0 si T croît ; pas de constante strictement contractante uniforme obtenue pour tout temps par cet argument.

## Limites et restrictions
Les paramètres proviennent des données mêmes auxquelles ils sont comparés. Le RMSE est descriptif, non une validation hors échantillon ; t0 initialise la courbe et est exclu du calcul après t0. Aucun poids de résidu, modèle de bruit, covariance, propagation de calibration ou sens probabiliste de stdev n'est rétabli. Les bornes d'optimisation ne sont pas des intervalles de confiance. Une faible erreur de courbe ne prouve pas une bonne identification des paramètres ou un mécanisme unique.

Le code épinglé de la bibliothèque d'estimation a fait l'objet d'un refus d'accès documenté par l'auteur. Cette revue n'a ni réessayé ni contourné cette restriction. L'archive et le notebook accessibles suffisent aux constats ci-dessus, pas à conclure sur l'algorithme interne d'estimation. Aucun transfert de garantie de l'ancien modèle de liaison vers ce système n'est justifié sans nouvelle hypothèse.

## Complément final : budget Euler ajouté à la synthèse
Nouvelle copie du replay et de ASSESSMENT_SLAC_FR.md examinée dans review_slac_20261105/final ; exécution réussie. Pour A(t)=kcat E(t),
S″=kie A S/(KM+S)+A² KM S/(KM+S)³.
Les deux termes sont positifs et leur somme est au plus C=V(kie+V/KM), V=kcat E0. En effet |S′|≤V et |∂S f|≤V/KM, tandis que ∂t f≤kie V. Le défaut local exact est ≤C h_i²/2. La non-expansion des transitions scalaires donne, pour une même initiale, erreur aux nœuds≤(C/2)∑h_i²≤ChT/2. L'hypothèse h_i≤KM/V assure aussi la positivité/invariance utilisée. L'enzyme reste évaluée analytiquement, pas avancée par Euler.

Avec h=1/200 minute, T=15 minutes et les décimales archivées considérées exactes, calcul Fraction : budget 0,009082451641253904 µM<0,01. Le replay retourne un écart maximal observé de0,0022792459853917535 µM aux instants de mesure. Aucun contrôle d'arrondi de exp, des opérations flottantes ou de la référence numérique n'est inclus dans la borne de troncature. La borne mathématique vise les nœuds ; aucune erreur d'interpolation entre nœuds n'est démontrée ici. Ces précisions ont été transmises à l'auteur.

Rédaction finale : recommander « modèle exporté explicitement spécifié » plutôt qu'« identifiable », qui pourrait être confondu avec une identifiabilité structurelle/statistique non étudiée. Aucune réserve sur les calculs ajoutés.

Dernière lecture du rapport gelé : l'auteur a intégré « explicitement spécifié », l'arrondi0,00908245 et la restriction aux nœuds sans interpolation. Accord final sur cette synthèse conditionnelle. La copie finale relue est conservée dans review_slac_20261105/final/ASSESSMENT_SLAC_FR.md. Toute adaptation ultérieure des chemins du paquet de livraison n'est pas assimilée à une nouvelle exécution vérifiée dans cette revue.
