# Revue indépendante du modèle jouet de liaison

5 novembre 2026. Revue du paquet certified-reaction-binding-20261105, sans modifier les sources. Reconstruction sur copie fraîche ; journaux et comparaison des sources reproduits dans verification/.

## Hypothèses et signification physique

Le modèle est cohérent comme liaison monosite R+L⇌C à ligand libre effectivement imposé par l’extérieur. Avec k_on≥0, k_off>0 et R_total>0, la fraction libre x=R/R_total satisfait le champ normalisé 1−(1+v)x, v=k_on L/k_off≥0, en temps s=k_off t. Le total récepteur est conservé, pas nécessairement le ligand. Le rapport distingue correctement un réservoir/protocole imposé d’une approximation de faible déplétion en système fermé.

Le pont formel prouve la somme nulle des deux flux et l’identité algébrique obtenue après substitution des fractions et normalisation. Il ne formalise pas une théorie générale des réseaux réactionnels, la conservation intégrée le long de toutes les solutions, ni une équivalence de trajectoires entre deux systèmes différentiels complets. Cela n’invalide pas l’algèbre, mais limite ce qui peut être annoncé comme prouvé dans Lean.

Aucune donnée expérimentale, identification de paramètres, preuve de mécanisme biologique ou prédiction thérapeutique n’intervient. Le modèle jouet ne couvre pas automatiquement la déplétion, la coopérativité, les états cachés ou le renouvellement du récepteur.

## Continu et Euler

La formule exponentielle à entrée constante vérifie dans Lean la dérivée attendue, la condition initiale et l’invariance de [0,1] pour un temps positif et un état initial physique. L’unicité générale du problème différentiel n’est pas un théorème de ce paquet. La substitution directe d’une entrée variable dans cette formule ne serait pas justifiée, et le rapport l’exclut.

L’application Euler Eτ(v,x)=τ+[1−τ(1+v)]x est un autre objet. Une propriété de cette récurrence n’est pas une borne de l’erreur de discrétisation Euler–ODE. Le pas τ est sans dimension ; en temps physique τ=k_off h.

## Garde exacte et contre-exemple

Sous τ≥0 et M≥0, l’invariance uniforme de [0,1] pour toutes les entrées v∈[0,M] est exactement équivalente à τ≤1 et τM≤1. Les deux valeurs aux extrémités de l’état, τ et 1−τv, fournissent nécessité et suffisance. La preuve inclut les frontières τ=0 et M=0 ; M≥0 évite une condition d’entrée vide.

La monotonie en l’état est différente : sa condition uniforme est τ≤1/(1+M). Une pente négative peut préserver [0,1]. La garde physique peut accepter τ=0, mais cela ne donne pas une contraction stricte. La complétude établie est celle de physicalGuard pour l’invariance de ce modèle, pas celle du checker combiné pour toute méthode ou tout réseau.

Pour τ=2/5 et M=3, les coefficients de pente sont 3/5 et −3/5. Le certificat signé accepte le taux 3/5 et le rayon 1, mais Eτ(3,1)=−1/5. Conservation des fractions et contraction n’assurent donc pas leur admissibilité. La valeur continue correspondante est environ 0,4014223885 : cette décimale n’est pas une preuve Lean d’un calcul numérique de l’exponentielle.

Pour τ=1/3, la garde accepte et le taux 2/3 est valide. La pente à v=3 vaut −1/3 : l’exemple est physique mais non monotone. Le seuil de monotonie à M=3 est 1/4, distinct de la garde d’invariance 1/3.

checkPhys doit rester interprété comme une garde spécifique à ce modèle. Pour ses coefficients arbitraires, il ne vérifie pas automatiquement leur identité avec une pente physique ; le raccord est prouvé séparément pour les coefficients concrets et v=3t.

## Suivi et indices

La récurrence sûre emploie v(n) pour calculer x(n+1), alors que l’erreur suivante vise f(v(n+1)). La preuve conserve explicitement cette dérive. La sensibilité de f(v)=1/(1+v) est bornée par 1 sur les entrées non négatives.

Ainsi e(n+1)≤(2/3)e(n)+|v(n+1)−v(n)|, puis, si chaque incrément est au plus δ, e(n)≤(2/3)^n e(0)+3δ(1−(2/3)^n). Le facteur 3 est 1/(1−2/3) et la somme est vide à n=0. δ désigne une variation d’entrée normalisée par pas, pas une vitesse physique.

La borne d’erreur vaut pour tout état initial réel. La conclusion distincte que la trajectoire reste physique exige x(0)∈[0,1], hypothèse présente. Il ne s’agit ni de suivi exact pour une entrée arbitraire, ni d’une estimation de l’écart Euler–ODE, ni d’une optimalité des constantes.

## Vérifications numériques et portée des audits

Le script d’expériences original exécuté dans la copie passe : contre-exemple, garde, 39083 évaluations de grille, trajectoires constante/rampe/commutations et suivi en Fraction. Les points de grille ne remplacent pas la preuve universelle. La rampe donne une erreur maximale affichée d’environ 0,08960 contre une contribution uniforme 0,15 ; les commutations illustrent une borne beaucoup moins informative.

La liste de 40 audits couvre bien les 40 théorèmes/lemmes des trois nouveaux modules. Aucun marqueur sorry/admit, nouvel axiome ou contournement natif n’est introduit dans les sources lues. Le script original de reconstruction est exécuté inchangé ; l’environnement d’import local est isolé et le binaire Lean ainsi que le commit mathlib sont contrôlés. Les objets mathlib sont réutilisés, pas intégralement reconstruits.

## Revue documentaire indépendante

Les sources étayent le contexte et les limites, pas les seuils numériques, qui sont dérivés et formalisés directement.

- La [page institutionnelle EMBL-EBI](https://www.ebi.ac.uk/training/online/courses/mathematical-modelling-biologists/introduction-to-three-mathematical-model-formalisms/ordinary-differential-equation-models/worked-example-ligand-receptor-binding/) a été ouverte directement : vitesses directe et inverse concordantes. Les équations présentées en images n’ont pas été inspectées dans cette revue.
- Le [résumé sur la page de Stroberg et Schnell](https://stroberg-lab.github.io/publication/stroberg2017a/) a été lu directement : il distingue précision des trajectoires approximatives et estimation des constantes. Cela soutient la prudence sur le pseudo-premier ordre sans fournir une validation du cas étudié.
- Les notices/extraits institutionnels ou éditeur de [IUPAC P04933](https://goldbook.iupac.org/terms/view/P04933), [Sandu 2001](https://www.sciencedirect.com/science/article/pii/S0021999101967506), [Greives et Zhou](https://pubmed.ncbi.nlm.nih.gov/24982141/), [Rao et Esposito](https://orbilu.uni.lu/bitstream/10993/12345/1/16RaoEspositoPRX.pdf) et [Monod, Wyman et Changeux](https://pubmed.ncbi.nlm.nih.gov/14343300/) ont été recoupés par recherche. Leurs contenus pertinents et identifiants concordent avec les usages prudents du dossier. Aucune nouvelle lecture intégrale de ces articles n’est revendiquée.
- La page PMC complémentaire de Hulme/Trevethick a présenté un contrôle de navigateur dans cette revue ; je ne revendique donc pas une lecture directe complémentaire.

Aucune réserve bibliographique substantielle identifiée à ce niveau d’accès. Les résultats ne constituent pas une validation biologique ou une revendication de nouveauté.

## Résultat final de reconstruction

Le rebuild.sh original termine avec code 0 : six modules reconstruits sur copie fraîche puis AuditReaction exécuté. verify_outputs.py termine avec code 0, statut PASS pour les 40 noms et les six sondes exactes true,false,false,true,true,true. Les axiomes transitifs se limitent à propext, Classical.choice et Quot.sound ; aucun sorryAx. Les diagnostics restants sont seulement des avertissements de style tactique. Les sources et scripts sont identiques au paquet gelé après reconstruction.

**Verdict : accord sur le jalon, ses hypothèses explicites et sa portée limitée. Aucun blocage mathématique ou de compilation.** Le rapport final doit conserver la distinction entre pont algébrique et théorèmes sur les trajectoires CRN complètes. Aucun résultat de précision Euler–ODE, de mécanisme biologique réel ou de nouveauté scientifique ne découle de cette validation.
