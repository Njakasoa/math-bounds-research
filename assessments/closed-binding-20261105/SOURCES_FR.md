# Sources et appréciation : liaison fermée contre approximation PFO

Consultation : 5 novembre 2026. Recherche documentaire en lecture seule ; aucun compte, paiement ni contournement de restriction. Les niveaux d’accès ci-dessous décrivent ce qui a réellement été lu, pas simplement ce qui est annoncé comme libre accès.

## Conclusion pour le laboratoire

Un benchmark reproductible de **validité du modèle**, avec observables et bilan de matière explicites, est pertinent. L’intégration exacte, les critères de faible déplétion et la possibilité de mauvaises estimations de constantes malgré des courbes proches sont déjà documentés. Même la génération de données exactes suivie d’un ajustement PFO possède des antécédents directs. Ne pas présenter ces éléments comme des découvertes nouvelles.

Le livrable utile est donc un contrôle de qualité : séparer erreur de discrétisation, erreur du modèle, et éventuelle erreur d’inférence ; annoncer la normalisation de chaque erreur ; exposer un cas où le modèle linéarisé viole le bilan de matière. Cela ne constitue aucune validation biologique.

## 1. Stroberg et Schnell, 2017 : antécédent central

W. Stroberg et S. Schnell, *On the validity and errors of the pseudo-first-order kinetics in ligand–receptor binding*, Mathematical Biosciences **287**, 3–11. DOI : https://doi.org/10.1016/j.mbs.2016.09.010 ; PMID 27693063.

### Accès effectivement obtenu

- Résumé directement lu sur le site de l’auteur : https://stroberg-lab.github.io/publication/stroberg2017a/.
- Notice/résumé indexés : https://pubmed.ncbi.nlm.nih.gov/27693063/. L’ouverture directe n’a rendu qu’une ligne institutionnelle ; le résultat de recherche contenait la notice complète.
- Version éditeur non lue intégralement : https://www.sciencedirect.com/science/article/pii/S0025556416301857 a renvoyé HTTP 403.
- Le PDF lié depuis la page de l’auteur, https://stroberg-lab.github.io/publication/Stroberg2017a/manuscript.pdf, a renvoyé HTTP 404. La variante avec dossier en minuscules n’a pas été accessible.
- Prépublication bioRxiv, DOI https://doi.org/10.1101/051136 : les URL HTML/PDF testées n’ont pas été accessibles par l’outil.
- **Texte intégral de la prépublication lu sur un miroir**, et non version finale garantie identique : https://studylib.net/doc/18285058/on-the-validity-and-errors-of-the-pseudo-first-order-kine... (URL indexée effectivement ouverte : les trois points font littéralement partie de l’URL retournée par l’outil, ce ne sont pas une troncature ajoutée ici ; URL canonique non vérifiée). Le document s’identifie comme prépublication du 30 avril 2016, sous CC-BY-ND 4.0. L’extraction altère certains symboles mathématiques. Aucun contrôle visuel du PDF original n’a été possible.

### Ce que le texte consulté établit

Les équations (3)–(5) fixent R0=R+C, L0=L+C et C(0)=0. Ks=koff/kon. Les équations (9)–(11) donnent la solution exacte quadratique intégrée. Le critère initial (17),(24) vise la déplétion relative maximale C∞/L0≪1. Le critère simplifié (30) est R0/(Ks+R0+L0)≪1. Il couvre notamment L0≫R0 ou Ks≫R0.

La section 5.1 étudie séparément une erreur rapportée à Cexact(t), puis son maximum temporel et sa limite à l’équilibre. Les barres de valeur absolue sont mal restituées par l’extraction ; le dénominateur Cexact, les erreurs positives représentées et les opérations maximum/limite sont lisibles. Ce n’est pas une borne uniforme explicite rapportée à R0.

Les sections 5.2–5.4 ajustent des données exactes par le modèle PFO, avec fenêtres et fréquences d’observation variables. Elles montrent une divergence entre précision des courbes et précision des constantes, particulièrement koff lorsque l’association devient peu sensible à la dissociation. Le résumé publié confirme cette distinction. Les numéros d’équation cités ici appartiennent au préprint consulté, pas nécessairement à la version éditée.

## 2. Du, 2024 : antécédent du benchmark de modèles

Y. Du, *Binding Curve Viewer: Visualizing the Equilibrium and Kinetics of Protein–Ligand Binding and Competitive Binding*, Journal of Chemical Information and Modeling **64**, 4180–4192. DOI : https://doi.org/10.1021/acs.jcim.4c00130.

**Accès : texte intégral effectivement lu** sur PMC : https://pmc.ncbi.nlm.nih.gov/articles/PMC11134506/. L’URL éditeur ACS a renvoyé 403. Le code et l’application sont référencés dans l’article : https://github.com/ydu-sci/Binding_Curve_Viewer et https://www.eplatton.net/binding-curve-viewer/ ; le code n’a pas été inspecté ni exécuté pendant cette recherche.

L’article juxtapose les cinétiques exactes du second ordre et PFO. Dans « Estimation of the Kinetic Properties from the Association Kinetic Experiment », il génère six mesures sans bruit par la solution exacte, ajuste kobs avec PFO, puis déduit kon et koff de deux concentrations de ligand. Le script indiqué est association_curve_fitting.py. La figure 3 quantifie les biais : pour son protocole particulier, l’amélioration de l’estimation de kon avec l’excès de ligand n’assure pas celle de koff. Cet exemple est un antécédent direct d’un benchmark de discordance de modèle. Les seuils numériques de ce protocole ne doivent pas être transformés en garanties universelles.

## 3. Spiegelberg et al., 2021 : équations lisibles directement

D. Spiegelberg, J. Stenberg, P. Richalet et M. Vanhove, *KD determination from time-resolved experiments on live cells with LigandTracer and reconciliation with end-point flow cytometry measurements*, European Biophysics Journal **50**, 979–991. DOI : https://doi.org/10.1007/s00249-021-01560-2.

**Accès : texte intégral éditeur effectivement lu**, avec équations textuelles : https://link.springer.com/article/10.1007/s00249-021-01560-2.

La section « Equations used », équations (2)–(3), définit explicitement L0 et R0 comme concentrations **totales**, écrit C′=kon(R0−C)(L0−C)−koff C et donne une forme intégrée exacte. Les équations (7)–(8) donnent la réduction PFO. L’équation (4) relie un signal normalisé à C/R0. Cette source est utilisée seulement pour vérifier les conventions et équations mathématiques ; les expériences biologiques ne valident pas le laboratoire présent. Elle renvoie à Vanhove et Vanhove (2018), DOI 10.1007/s00249-018-1318-y ; ce dernier article n’a pas été lu intégralement ici.

## 4. Autres pistes, avec limites explicites

- *Analyzing Kinetic Binding Data*, Assay Guidance Manual : https://www.ncbi.nlm.nih.gov/books/NBK569501/. Le résultat indexé indique une déplétion inférieure à 20 %, idéalement 10 %, pour certaines équations. L’ouverture a rencontré une page reCAPTCHA : aucun CAPTCHA résolu, pas de lecture intégrale, pas d’utilisation comme preuve d’un seuil universel.
- *Modelling ligand depletion for simultaneous affinity and binding site quantification on cells and tissue* (2023), DOI 10.1038/s41598-023-37015-1 : https://pmc.ncbi.nlm.nih.gov/articles/PMC10282064/ et https://www.nature.com/articles/s41598-023-37015-1. Résultats indexés seulement ; PMC a présenté reCAPTCHA et Nature une redirection d’authentification inaccessible. Non utilisé pour une conclusion détaillée.
- CMI Binding Simulator : https://cmi-hms.github.io/binding-simulator/. Documentation intégralement accessible ; illustre déjà mass balance, solution quadratique intégrée et ajustement de modèles. Outil institutionnel, **pas publication évaluée par les pairs** ; non utilisé pour attribuer une priorité scientifique.

## 5. Traduction des variables et distinction des erreurs

Les calculs suivants sont notre mise en correspondance algébrique, non des citations ou résultats attribués aux articles.

Soit Rtot>0, Ltot>0, kon>0, koff>0, C la concentration de complexe, x=Rlibre/Rtot=1−C/Rtot et τ=koff t. Alors :

- μ=Ltot/Rtot ; α=kon Rtot/koff=Rtot/Kd ; Kd=koff/kon.
- Llibre/Rtot=μ−1+x.
- x′=1−x−αx(μ−1+x), avec x≥max(0,1−μ).
- Pour C0=0, x0=1 et Ltot=Llibre(0). L’approximation xP′=1−(1+αμ)xP fige donc sans ambiguïté le ligand initial dans le benchmark retenu.

La correspondance au préprint est R0′=Rtot/Kd=α et L0′=Ltot/Kd=αμ. Son paramètre simplifié devient

ε=α/[1+α(1+μ)].

L’enveloppe candidate du laboratoire est B=α/[4(1+αμ)]=ε/[4(1−ε)]. Cette identité ne transforme pas le critère publié en preuve de B. Elle montre que les deux formulations exploitent essentiellement le même régime de faible déplétion, avec des objets et niveaux de garantie distincts.

Trois quantités ne doivent pas être confondues :

1. Déplétion relative du ligand : C/Ltot=(1−x)/μ.
2. Erreur absolue de fraction de récepteurs : |C−CP|/Rtot=|x−xP|. C’est la quantité visée par B.
3. Erreur relative du complexe : |C−CP|/C=|x−xP|/(1−x), pour C>0. Elle peut être importante quand le signal est faible. À t=0, C0=0 impose une convention explicite : exclusion du point ou limite, jamais une division naïve par zéro.

L’erreur sur kon ou koff est une quatrième quantité, dépendant aussi de l’identifiabilité, de la fenêtre, des concentrations, des paramètres fixés/libres et du bruit. B seul ne la contrôle pas.

### Formule exacte directement utilisable pour C0=0

La solution quadratique intégrée des sources peut se réécrire dans nos variables avec q=1−x, s=1+μ+1/α, D=√(s²−4μ), q−=(s−D)/2 et q+=(s+D)/2 :

q(τ)=q−[1−exp(−αDτ)]/[1−(q−/q+)exp(−αDτ)].

Le calcul q−=2μ/(s+D) évite la soustraction de deux nombres proches. Pour les mêmes conditions initiales, qP(τ)=[αμ/(1+αμ)][1−exp(−(1+αμ)τ)]. Les deux expressions valent zéro à l’origine. Ce sont des reformulations de solutions connues, pas de nouveaux résultats.

### Cas où des complexes sont présents initialement

Si C0>0, alors Llibre(0)=Ltot−C0 et Llibre(0)/Rtot=μ−1+x0. Figer Ltot conduit à l’équation PFO ci-dessus ; figer le ligand **libre initial** conduit à xP′=1−[1+α(μ−1+x0)]xP. Ce sont deux approximations différentes. Les bornes ne se transfèrent pas automatiquement de l’une à l’autre. Le benchmark principal choisit C0=0 pour éviter cette ambiguïté.

## 6. Protocole utile, borné à la validité du modèle

- Référence : solution exacte de la cinétique fermée, avec un intégrateur indépendant comme contrôle numérique secondaire.
- Modèle à tester : solution PFO exacte d’abord ; Euler seulement ensuite. Ainsi l’erreur de discrétisation n’est pas confondue avec l’erreur du modèle.
- Observables minimales : x, C/Rtot, Llibre/Rtot, erreur absolue maximale et stationnaire, violation du domaine physique. Le maximum sur une grille reste une observation numérique, pas une certification de supremum.
- Repères : excès de ligand, faible α sans excès, et ligand limitant à forte α. Indiquer α, μ, C0 et la fenêtre sans unités ambiguës.
- Cas fort retenu : α=10, μ=0,1, x0=1. La cinétique fermée exige x≥0,9 ; PFO tend vers 0,5. Le modèle PFO prévoit alors C/Rtot=0,5 malgré Ltot/Rtot=0,1. Un pas Euler plus petit ne peut corriger ce défaut du modèle continu.
- Si une étude d’inférence est ajoutée ultérieurement, la présenter comme volet distinct, avec contraintes, multi-démarrages et diagnostic de conditionnement. Ne pas la déduire d’une faible erreur de trajectoire.

Ce protocole apporte une valeur pédagogique et de test logiciel traçable. Il ne prétend ni établir une priorité, ni découvrir un nouveau mécanisme, ni valider une application biologique.
