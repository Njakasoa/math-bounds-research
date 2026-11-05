# Décision de recherche : fermer le bilan de ligand avant d'ajouter des preuves numériques

## Évaluation franche
Pour un mélange effectivement fermé où le ligand peut être déplété, fermer son bilan améliore la pertinence chimique du modèle jouet. Pour un vrai réservoir maintenu, ce serait au contraire le mauvais choix. La première décision porte donc sur les conditions physiques aux limites, pas sur une préférence générale pour le modèle le plus complexe. En revanche, les solutions de liaison avec déplétion, les critères pseudo-premier ordre et les comparaisons de courbes/paramètres existent déjà dans la littérature et dans Binding Curve Viewer. Une nouvelle série de tracés ou une grande formalisation Lean, à elle seule, ne serait pas une avancée scientifique.

La proposition utile est plus étroite : un test de bilan de matière et un budget d'erreur de modèle, avec une observable et une tolérance explicites. Cette note constitue une analyse mathématique relue et un petit jeu de tests reproductibles, pas un nouveau jalon de preuves Lean ni une validation biologique.

## Modèles comparés, à mélange initial identique
Même réseau monosite R+L⇌C, bien mélangé, loi d'action de masse, k_on≥0, k_off>0, R_total>0. Dans le système fermé, R+C=R_total et L+C=L_total. Aucune création/destruction, aucun autre état du récepteur ni réaction concurrente.

Poser x=R/R_total, μ=L_total/R_total≥0, α=k_on R_total/k_off≥0 et s=k_off t. Alors
C/R_total=1−x et L/R_total=μ−1+x.
L'intervalle physique est Iμ=[max(0,1−μ),1], et le champ fermé est
z′=1−z−αz(μ−1+z).

La comparaison principale part de C(0)=0, donc z(0)=y(0)=1. Le modèle pseudo-premier ordre comparé maintient artificiellement le ligand libre à L_total :
y′=1−(1+αμ)y.
Les mélanges initiaux coïncident ici. Si des complexes existent déjà au départ, L_libre(0)≠L_total : figer le ligand libre initial définit un autre modèle de référence, auquel les signes et bornes ci-dessous ne doivent pas être transférés automatiquement.

## Test de bilan à l’équilibre : un rejet à long terme, pas sur tout horizon
Pour 0<μ<1, le système fermé exige x≥1−μ. Le modèle à ligand imposé prévoit y∞=1/(1+αμ). Cet équilibre viole la capacité stœchiométrique du système fermé exactement lorsque α(1−μ)>1.

Exemple α=10, μ=1/10 : la fraction libre fermée doit rester au moins 9/10, mais le modèle ouvert prévoit 1/2. Son complexe prédit vaut donc la moitié du total récepteur, alors que le total ligand n'en permet qu'un dixième. L'équilibre fermé vaut (4+√26)/10≈0,909902 ; l'écart d'équilibre est environ 0,409902.

Le modèle ouvert n'est pas faux pour un réservoir réellement maintenu. Cette contradiction exclut son utilisation pour la prédiction stationnaire ou à suffisamment long terme de ce système fermé ; elle n'interdit pas automatiquement une approximation sur un horizon court. Réduire le pas Euler ne peut pas corriger cette erreur : les équilibres des deux modèles restent différents. Inversement, ne pas violer cette capacité ne suffit pas à valider l'approximation. Dans cet exemple, y(s)=1/2+(1/2)exp(−2s) franchit la limite 9/10 à s_cap=(1/2)log(5/4)≈0,111572. Avant ce temps, ce seul test de capacité ne rejette pas la trajectoire ; l'erreur pour l'observable choisie et l'horizon demandé doit encore être comparée à la tolérance.

## Budget d'erreur de modèle : observable explicite
Sur Iμ, le champ fermé préserve les concentrations admissibles et sa dérivée est au plus −1−α|μ−1|. Il possède un unique équilibre physique. Cette observation est une analyse élémentaire du modèle, non une nouvelle propriété de la chimie.

Pour d=z−y, λ=1+αμ et un départ commun :
d′=−λd+αz(1−z), d(0)=0.
La variation des constantes donne
 d(s)=α∫₀ˢ exp(−λ(s−r))z(r)(1−z(r))dr.
Comme z∈Iμ⊂[0,1], définir q(μ)=μ(1−μ) si 0≤μ≤1/2, et q(μ)=1/4 sinon. Alors, pour tout s≥0,
0≤z(s)−y(s)≤[αq(μ)/(1+αμ)]·[1−exp(−(1+αμ)s)].

En particulier, le plafond plus simple B=α/[4(1+αμ)] est toujours suffisant, et B≤1/(4μ) si μ>0. Le même scénario α=10, μ=0,1 illustre l’importance de l’horizon : pour 0≤s≤1/100, la borne affinée donne d(s)≤(9/20)(1−exp(−2s))≤(9/10)s≤9/1000<0,01. Le modèle approché satisfait donc ce budget absolu sur cet horizon court, malgré son échec à long terme.

Pour un horizon fini T, on peut conserver le facteur 1−exp(−(1+αμ)T), au lieu du plafond uniforme plus grossier. Cette erreur est une erreur absolue rapportée au total récepteur, identique pour fractions libre et liée. Ce n'est pas une erreur relative rapportée à la petite quantité de complexe.

Pour garantir au plus 0,01 du total récepteur, soit un point de pourcentage de fraction, μ≥25 est une condition suffisante indépendante de α. Elle n'est pas nécessaire. Pour k_on>0, K_d=k_off/k_on et ε=R_total/(K_d+R_total+L_total)=α/[1+α(1+μ)]. Au cas k_on=0, on définit directement ε=0 par cette dernière expression, sans diviser par k_on. Alors le plafond simple s'écrit B=ε/[4(1−ε)]. Ainsi ε≤1/26 suffit à ce budget de 0,01. C'est une traduction de notre majoration absolue dans les variables d'un régime classique, pas une nouvelle région de validité ni une citation d'une borne fournie telle quelle par les auteurs.

## Exemples contrastés qui changent la décision
- α=10, μ=0,1 : le modèle ouvert viole le bilan de ligand. Écart d'équilibre≈0,409902 ; plafond affiné 0,45. Il faut garder le modèle fermé pour une prédiction stationnaire ou au-delà du franchissement de capacité ; le choix sur un horizon court dépend encore de la tolérance.
- α=1, μ=1 : pas de violation de capacité, mais écart d'équilibre≈0,118034 ; plafond 0,125. Une tolérance de 0,01 n'est pas satisfaite à l'équilibre, ni uniformément pour tout temps.
- α=1, μ=25 : écart d'équilibre≈0,001475 ; plafond 1/104≈0,009615. Le budget absolu de 0,01 est garanti sous les hypothèses. Cela ne garantit pas l'identification correcte de k_on ou k_off.
- α=1, μ=0,001 : écart absolu d'équilibre≈0,000499, mais erreur relative de complexe≈99,85 %. Une petite erreur de fraction totale peut donc être inacceptable pour l'observable « quantité de complexe relative ».
- α=2, μ=1 : équilibres fermé 1/2 et ouvert 1/3, écart exact 1/6 égal au plafond simple. Une borne de modèle ne doit pas être remplacée par une promesse arbitrairement plus petite.

Tous ces exemples sont sans données expérimentales. Les décimales sont des présentations de résultats encadrés en rationnels.

## Antériorités et ce que nous n'ajoutons pas
Stroberg et Schnell étudient déjà le critère de déplétion et distinguent fidélité des trajectoires et erreur d'estimation des constantes. Leur critère de déplétion relative du ligand et leurs erreurs relatives au complexe ne sont pas notre norme absolue rapportée à R_total. Binding Curve Viewer (Du, 2024) propose déjà des comparaisons exactes/pseudo-premier ordre et des exemples d'ajustement de paramètres. SOURCES_FR.md précise textes, versions et niveaux de consultation.

La contribution pratique de cette note est uniquement de rendre le choix d'hypothèse testable dans le laboratoire existant. Nous ne réimplémentons pas un outil d'ajustement, ne revendiquons aucune nouveauté et n'inférons pas de résultats empiriques à partir du modèle jouet.

## Test reproductible et prochain critère de décision
check_closed_binding.py vérifie 48 couples de paramètres par arithmétique rationnelle : intervalle physique, encadrement de la racine d'équilibre, signe/plafond d'écart, critère de violation de capacité et contraste entre erreurs absolue et relative. La dichotomie utilise continuité et monotonie du champ, justifiées dans l'analyse ; ce n'est pas un certificat Lean. Les tests d'équilibre ne constituent pas une intégration numérique indépendante du système original à trois espèces. La borne transitoire est un raisonnement analytique séparé.

Avant une nouvelle formalisation lourde, il faut établir si le montage est réellement ouvert ou fermé, puis fixer ce qui doit être prédit : fraction totale, petite quantité de complexe relative, constante cinétique, ou autre observable ; préciser l’horizon temporel, la tolérance, les totaux, les conditions initiales et les paramètres connus. Si un jeu de données ou une décision concrète l'exige, le prochain test utile comparera le système original à trois espèces, sa réduction et le modèle approché, avec les mêmes conditions initiales. Sans cela, approfondir les preuves numériques serait prématuré.
