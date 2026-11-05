# Un modèle jouet réactionnel : liaison réversible à un site

## Question et résultat ciblé
Peut-on utiliser le certificat de contraction et la borne de suivi pour un réseau réactionnel précisément défini ? Oui, pour une discrétisation d'un modèle monosite à ligand imposé, mais la contraction seule ne garantit pas l'admissibilité des concentrations. Le contre-exemple exact ci-dessous rend cette limite testable. Il ne s'agit ni d'une découverte des lois de liaison, ni d'une validation biologique.

## Classe de modèles et hypothèses physiques
Le réseau est R+L ⇌ C, avec constantes k_on≥0 et k_off>0. R désigne le récepteur libre, C le complexe, L le ligand. La loi d'action de masse donne Ṙ=−k_on LR+k_off C et Ċ=−Ṙ. Le total récepteur R_total=R+C est positif et conservé : il n'y a ni synthèse, ni destruction, ni autre état du récepteur.

La concentration libre L(t) est ici une entrée non négative effectivement imposée par l'extérieur. Le ligand n'est donc pas supposé conservé dans ce modèle ouvert. Un réservoir maintenu à concentration fixée et un protocole temporel imposé doivent être distingués. L'approximation « ligand en grand excès dans un système fermé » est une autre hypothèse : elle n'est pas automatiquement exacte.

En posant x=R/R_total, s=k_off t et v=k_on L/k_off, le champ normalisé devient dx/ds=1−(1+v)x. L'état physique est x∈[0,1], la fraction liée vaut 1−x. L'équilibre à entrée constante est f(v)=1/(1+v). Pour une entrée variable, cette formule est seulement la cible instantanée.

Les calculs sont sans dimension et sans paramètres expérimentaux ajustés. Le modèle est une classe pédagogique de cinétique de masse, pas la description établie d'un système vivant particulier.

## Dynamique continue et Euler : deux objets différents
Pour v constant, la solution analytique est
x(s)=f(v)+(x(0)−f(v))exp(−(1+v)s).
Elle préserve [0,1] pour tout s≥0 si l'état initial y appartient. Cette formule ne s'applique pas avec v(t) simplement substitué lorsque l'entrée varie continûment. Pour une entrée constante par morceaux, elle s'applique séparément sur chaque intervalle.

Euler explicite avec pas dimensionnel h et τ=k_off h donne
Eτ(v,x)=τ+[1−τ(1+v)]x.
C'est cette application polynomiale discrète que le checker certifie. Une garantie sur Euler n'est pas une borne de son erreur par rapport à l'ODE.

Pour τ≥0 et v∈[0,M], les conditions exactes sont :
- Préservation de [0,1] : τ≤1 et τM≤1.
- Monotonie en l'état pour chaque entrée : τ≤1/(1+M), condition plus forte.
- Contraction uniforme : max(|1−τ|,|1−τ(1+M)|)<1.

L'invariance se vérifie aux deux extrémités en x : Eτ(v,0)=τ et Eτ(v,1)=1−τv. Une pente négative n'implique donc pas à elle seule une concentration négative. En unités physiques, l'invariance exige h k_off≤1 et h k_on L_max≤1.

## Benchmark falsifiable et garde physique
Fixer M=3 et x(0)=1.

1. Avec τ=2/5, les coefficients Bernstein de degré 1 de la pente sont [3/5,−3/5]. Le checker signé accepte κ=3/5 et rayon 1. Pourtant Eτ(3,1)=−1/5, hors du domaine physique. La fraction liée calculée vaut 6/5 : leur somme reste 1, mais les fractions ne sont pas admissibles. Conservation et contraction ne suffisent pas.
2. Au même instant, la formule continue vaut 1/4+(3/4)exp(−8/5)≈0,4014223885. La négativité provient du schéma, pas de la réaction continue.
3. Avec τ=1/3, le checker accepte κ=2/3 et rayon 1 ; [0,1] est invariant. La pente à v=3 vaut pourtant −1/3 : la positivité physique ne requiert pas la monotonie de l'application discrète.

Une garde rationnelle spécifique au modèle vérifie 0≤τ, 0≤M, τ≤1 et τM≤1. Elle rejette le premier cas et accepte le second. Sa combinaison avec le checker ne devient pas un certificat générique de réseaux réactionnels : l'identité entre coefficients et application réelle demeure une obligation séparée, prouvée ici avec v=3t et t∈[0,1]. Le test attendu est précis : accepter la contraction du premier cas, mais refuser son admissibilité physique.

## Suivi pour le pas admissible
Pour τ=1/3, v(n)∈[0,3], la trajectoire discrète reste physique si elle le commence. La cible satisfait |f(u)−f(v)|≤|u−v| pour u,v≥0. Avec e(n)=|x(n)−f(v(n))| et |v(n+1)−v(n)|≤δ, la borne est

e(n)≤(2/3)^n e(0)+3δ(1−(2/3)^n).

La mise à jour utilise v(n), tandis que l'erreur suivante est mesurée contre f(v(n+1)). Ce décalage est conservé. La borne contrôle le suivi par Euler de la cible instantanée, pas l'écart Euler–ODE. Les constantes ne sont pas annoncées optimales. Pour des variations rapides, elle peut être très grossière.

## Tests et limites de validation
Les assertions discrètes sont calculées en rationnels exacts : contre-exemple, garde, grille finie, trajectoires constantes, rampe et commutations. La grille finie ne remplace pas les preuves universelles. L'exponentielle et les décimales imprimées sont des approximations de présentation.

Des données pourraient tester les prédictions du modèle : à ligand réellement fixé, relaxation monoexponentielle, taux k_off+k_on L, fraction libre d'équilibre k_off/(k_off+k_on L), et total récepteur constant. Des écarts établis sous les hypothèses du modèle le réfuteraient. Un bon ajustement ne prouverait toutefois ni unicité du mécanisme ni identification correcte des paramètres. Aucun jeu de données n'est analysé ici.

La déplétion du ligand dans un système fermé, des états cachés, la coopérativité, des effets spatiaux ou un renouvellement des récepteurs sortent de cette réduction affine. Ils nécessitent un autre modèle et de nouvelles vérifications. Aucun résultat sur des réseaux généraux, aucune validation biologique, aucun certificat de précision numérique, et aucune revendication de nouveauté ne sont déduits. Les antériorités et leur niveau de consultation sont consignés dans SOURCES_FR.md.

Validation : le script original complet a été reconstruit indépendamment sur copie fraîche, avec succès. Les 40 déclarations nouvelles auditées utilisent seulement propext, Classical.choice et Quot.sound ; les six sondes et les expériences exactes passent.

Portée formelle précise : les flux opposés et la substitution algébrique sont vérifiés, ainsi que la dérivée, la condition initiale et l’invariance de la formule analytique. Cela ne constitue pas une formalisation générale de la conservation intégrée, de l’équivalence entre trajectoires du réseau et du modèle réduit, ni de l’unicité du problème à valeur initiale. Ces distinctions empêchent de transformer ce benchmark en validation générale de réseaux réactionnels.
