# Sources et niveau de vérification documentaire

Consultation : 5 novembre 2026. Cette note distingue les passages effectivement consultés des textes seulement signalés par un moteur de recherche. Un extrait indexé ne constitue pas une lecture directe du document. Les courts extraits anglais ci-dessous sont reproduits tels que renvoyés par les sources ou leur indexation ; les explications françaises sont des paraphrases.

## 1. Loi d’action de masse : EMBL-EBI

**Source :** [Guided example: ligand-receptor binding](https://www.ebi.ac.uk/training/online/courses/mathematical-modelling-biologists/introduction-to-three-mathematical-model-formalisms/ordinary-differential-equation-models/worked-example-ligand-receptor-binding/), cours institutionnel *Mathematical modelling for biologists*.

**Lecture réelle :** page institutionnelle ouverte directement. Les sections décrivant les espèces, la réaction, les deux vitesses et le lien avec les équations différentielles ont été consultées. Les trois équations différentielles elles-mêmes sont des images et n’ont pas été inspectées ; les vitesses sont, elles, données en texte.

**Court passage exact :** « Ligand + Receptor ⇌ Active receptor ».

**Appui précis :** vitesse directe proportionnelle au produit ligand × récepteur libre ; vitesse inverse proportionnelle au complexe. La conservation R+C=R_total se déduit de la stœchiométrie du modèle retenu. L’intitulé pédagogique « Active receptor » n’autorise pas à identifier toute liaison à une activation biologique.

## 2. Définition pseudo-premier ordre : IUPAC

**Source :** [Gold Book, « pseudo rate constant », P04933](https://goldbook.iupac.org/terms/view/P04933).

**Lecture réelle :** définition et formule visibles dans les extraits indexés du site officiel. Les ouvertures directes des versions HTML et texte ont échoué avec une réponse HTTP 403. Aucune lecture directe de ces pages n’est revendiquée.

**Court passage exact, extrait indexé :** « The term pseudo rate constant is particularly useful when the concentration of one reactant is much greater than that of another. »

**Appui précis :** le coefficient k[A] est appelé pseudo-premier ordre par rapport à B lorsque la vitesse est k[A][B]. Cette définition ne justifie pas, à elle seule, que la concentration libre du ligand reste constante dans un cas particulier.

## 3. Déplétion et validité de l’approximation : Stroberg et Schnell

**Source :** W. Stroberg et S. Schnell, *On the validity and errors of the pseudo-first-order kinetics in ligand–receptor binding*, Mathematical Biosciences 287 (2017), 3–11, DOI 10.1016/j.mbs.2016.09.010. [Page de l’auteur](https://stroberg-lab.github.io/publication/stroberg2017a/) ; [page éditeur](https://www.sciencedirect.com/science/article/pii/S0025556416301857).

**Lecture réelle :** page de l’auteur ouverte directement et résumé lu. Des extraits de l’article, dont la réaction 1:1 et la loi d’action de masse, étaient aussi indexés chez l’éditeur. Le texte intégral n’a pas été lu : ouverture éditeur en HTTP 403, PDF lié depuis la page auteur en HTTP 404. Les détails bibliographiques de volume et pagination proviennent de la notice indexée de l’éditeur.

**Court passage exact, résumé directement consulté :** « large errors are possible in estimated kinetic constants, even when the linearized and exact rate equations provide nearly identical solutions. »

**Appui précis :** distinguer validité des trajectoires approximatives et validité de l’estimation des constantes. Aucune condition quantitative détaillée de validité, non vérifiée dans le texte intégral, n’est reprise ici.

## 4. Concentrations imposées et système ouvert : Rao et Esposito

**Source :** R. Rao et M. Esposito, *Nonequilibrium Thermodynamics of Chemical Reaction Networks: Wisdom from Stochastic Thermodynamics*, Physical Review X 6, 041064 (2016), DOI 10.1103/PhysRevX.6.041064. [PDF signalé dans le dépôt institutionnel](https://orbilu.uni.lu/bitstream/10993/12345/1/16RaoEspositoPRX.pdf).

**Lecture réelle :** extraits indexés du PDF uniquement, notamment le passage autour des équations (8) et (9). L’ouverture directe du PDF a échoué avec HTTP 502. Il ne faut donc pas décrire cette vérification comme une lecture du PDF ou de l’article intégral.

**Courts passages exacts, extraits indexés :** « In nondriven open CRNs, the chemostatted species have constant concentrations » ; « In driven open CRNs, the chemostatted concentrations change over time ».

**Appui précis :** l’extrait distingue concentrations chemostattées constantes et protocole temporel imposé ; il ajoute des courants externes au bilan des espèces chemostattées. Cela étaye la distinction conceptuelle entre ligand réellement imposé et ligand seulement supposé peu déplété. Aucun résultat thermodynamique de l’article n’est utilisé dans le benchmark.

## 5. Positivité numérique : Sandu

**Source :** A. Sandu, *Positive Numerical Integration Methods for Chemical Kinetic Systems*, Journal of Computational Physics 170 (2001), 589–602, DOI 10.1006/jcph.2001.6750. [Page éditeur](https://www.sciencedirect.com/science/article/pii/S0021999101967506).

**Lecture réelle :** notice et résumé indexés uniquement. L’ouverture directe de la page éditeur a échoué avec HTTP 403. Les pages 589–602 et le volume 170 ont été recoupés dans des bibliographies indexées, pas sur une page du texte intégral.

**Court passage exact, résumé indexé :** « Chemical kinetics conserves mass and renders nonnegative solutions; a good numerical simulation would ideally produce mass-balanced, positive concentration vectors. »

**Appui précis :** conservation et positivité sont des propriétés numériques à contrôler. La source n’est pas utilisée comme preuve des seuils Euler particuliers de ce dossier. Les conditions de contraction, d’invariance de [0,1] et de monotonie sont dérivées directement du modèle dans les fichiers du projet.

## 6. États cachés et ambiguïté mécanistique : Greives et Zhou

**Source :** N. Greives et H.-X. Zhou, *Both protein dynamics and ligand concentration can shift the binding mechanism between conformational selection and induced fit*, PNAS 111 (2014), 10197–10202, DOI 10.1073/pnas.1407545111. [Texte signalé sur PMC](https://pmc.ncbi.nlm.nih.gov/articles/PMC4104862/).

**Lecture réelle :** résumé et passages assez étendus du texte intégral renvoyés dans les résultats de recherche, notamment la section sur l’ajustement monoexponentiel, l’équation [2] et les commentaires des figures 3 et 4. Ce sont des extraits indexés : l’ouverture directe de PMC a renvoyé une vérification de navigateur, pas l’article. Aucune lecture directe intégrale n’est revendiquée.

**Court passage exact, extrait indexé :** « can be fit to a single exponential, with the apparent rate constant exhibiting a linear dependence on ligand concentration. »

**Appui précis :** leur modèle simulé comporte transitions conformationnelles et diffusion, tout en présentant ces signatures cinétiques simples. Ces signatures ne suffisent donc pas à établir le mécanisme élémentaire utilisé ici. C’est une mise en garde sur l’interprétation du modèle, pas une validation de celui-ci.

## 7. Coopérativité : Monod, Wyman et Changeux

**Source :** J. Monod, J. Wyman et J.-P. Changeux, *On the Nature of Allosteric Transitions: A Plausible Model*, Journal of Molecular Biology 12 (1965), 88–118, DOI 10.1016/S0022-2836(65)80285-6. [Notice PubMed](https://pubmed.ncbi.nlm.nih.gov/14343300/) ; [PDF institutionnel signalé](https://www.unige.ch/sciences/biochimie/Edelstein/Monod%20Wyman%20Changeux%201965.pdf).

**Lecture réelle :** notice bibliographique et extrait indexé de la première page du PDF. L’ouverture du PDF a échoué en raison de sa taille ; aucune lecture du modèle complet n’a été effectuée.

**Court passage exact, extrait indexé :** « indirect interactions between distinct specific binding-sites (allosteric effects) ».

**Appui précis :** référence primaire historique aux interactions entre sites et transitions allostériques, absentes du modèle scalaire retenu. Aucune équation ni prédiction détaillée du modèle MWC n’est utilisée.

## Source complémentaire consultée

Hulme et Trevethick, *Ligand binding assays at equilibrium: validation and interpretation* (2010), [PMC](https://pmc.ncbi.nlm.nih.gov/articles/PMC3000649/), DOI 10.1111/j.1476-5381.2009.00604.x. La page du texte intégral a été ouverte directement ; le début et la section « Theoretical foundations of receptor binding studies », jusqu’aux équations (1a)/(1b), ont été consultés, pas l’article entier. Il s’agit d’une revue, non d’un article de recherche original. Le passage consulté donne la conservation du récepteur et les hypothèses de population homogène et accessible. Cette revue peut servir de contexte complémentaire ; le dossier n’en tire aucun protocole expérimental.

## Portée de la bibliographie

La bibliographie motive un modèle abstrait et documente ses limites. Elle ne certifie ni son adéquation biologique, ni l’identifiabilité de ses paramètres, ni la précision d’Euler. L’accord d’un checker de contraction ne remplace pas une preuve de positivité. Une entrée imposée ne doit pas être confondue avec la concentration totale ajoutée dans un système fermé. Aucun passage documentaire ne transforme ce benchmark en validation expérimentale.
