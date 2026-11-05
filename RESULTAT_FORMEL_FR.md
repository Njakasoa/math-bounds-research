# Subdivision rationnelle : équivalence et réalisation locale vérifiées en Lean

5 novembre 2026. Recherche mathématique abstraite. Aucune nouveauté mathématique ou priorité de formalisation revendiquée.

## Résultat principal

Pour toute famille finie S₁,…,Sₖ de polynômes rationnels en m variables, les deux conditions suivantes sont équivalentes :

1. Les Sᵢ n'ont aucun zéro commun sur le pavé réel [−1,1]ᵐ.
2. Il existe une subdivision uniforme finie de ce pavé en cubes rationnels telle que, dans chaque cube, un multiplicateur rationnel constant t et un indice i vérifient
   ‖1−t Sᵢ(c+v/N)‖₁<1.

La norme est la somme des valeurs absolues des coefficients **regroupés**. Les cubes ont rayon 1/N et centres cⱼ=−1+(2aⱼ+1)/N, avec 0≤aⱼ<N. Leur couverture de tout le pavé est prouvée, y compris les frontières. Le théorème vaut pour tous m,k naturels, avec les cas vides traités par les propositions elles-mêmes.

**Théorème Lean :** `LocalAtlas.no_common_real_zero_iff_grid`.

Il s'agit d'une caractérisation de la possibilité de certifier **localement après subdivision**, pas d'une caractérisation d'un système polynomial unique sur tout le domaine.

## Le raccord au checker est également prouvé

`LocalAtlas.exists_checked_grid` déduit de la seule absence de zéro commun réel :

- Un entier N>0 et, dans chaque cube, une famille fixe de témoins polynomiaux rationnels.
- Une application polynomiale à **un seul état**, acceptée par le checker rationnel archivé.
- Pour chaque entrée locale admissible, un unique état fixe dans sa boîte certifiée.
- L'identité de Bézout ΣSᵢ(u)yᵢ=1, où toutes les sorties polynomiales utilisent ce même état.

Les témoins du cube sont choisis avant ses entrées. L'état, lui, dépend de l'entrée. Les expressions sont normalisées avant l'application du checker, pour conserver les annulations de coefficients.

La sélection globale et la normalisation canonique sont non calculatoires dans cette formalisation. Le checker d'une syntaxe fournie est exécutable ; cette preuve ne constitue pas un synthétiseur Lean extrait de bout en bout. Le générateur Python de la note analytique antérieure reste un programme séparé.

## Briques vérifiées, sans hypothèse de témoin

- **Variation des coefficients.** Pour 0≤h≤1 et |cⱼ|≤1 :
  ‖S(c+hv)−S(c)‖₁≤h C(S), avec C(S)=Σα|sα|(2^{|α|}−1).
  La norme est construite sur les véritables polynômes rationnels, pas fournie comme une hypothèse abstraite.
- **Normalisation.** Si h C(S)<|S(c)|, alors t=1/S(c) donne le résidu strictement inférieur à 1. Le dénominateur non nul est déduit.
- **Marge uniforme.** La compacité fournit δ>0 tel qu'en chaque point au moins un |Sᵢ|≥δ.
- **Subdivision.** Une grille rationnelle assez fine satisfait l'inégalité sur tous ses cubes. Sa couverture est démontrée par un argument de partie entière.
- **Réciproque.** Un zéro commun réel ferait prendre la valeur 1 au résidu d'un cube qui le contient, contradiction avec sa norme <1.

La preuve Lean d'existence utilise une marge issue de la somme des |Sᵢ| divisée par k, et une majoration par la somme des C(Sᵢ). Elle ne revendique pas l'optimalité de cette borne, ni la formalisation exacte du choix « minimum du maximum » et de la borne maximale plus fine présentés dans la note analytique.

## Exemple exact et limite globale

Pour la cible 1/(1+4u²) sur [−1,1], deux cellules suffisent : [−1,0] et [0,1]. Avec u=±1/2+v/2 :

- S local = 2±2v+v².
- T(v)=1/2∓v/2+v²/4.
- ST=1+v⁴/4, donc résidu q=−v⁴/4.
- Le taux certifié est 1/4 et le rayon d'état 4/3.

`TwoCellCheckedRealization.checked_full_interval_realization` relie effectivement le même état vectoriel accepté par le checker à la sortie prescrite, pour chaque |u|≤1. Une syntaxe de sortie rationnelle et son évaluation sont également prouvées. La couverture et l'accord des sorties à la frontière u=0 sont établis.

`TwoCellObstruction.no_scalar_multiplier` exclut tout multiplicateur polynomial global sur le cube initial : le résidu vaut nécessairement 1 au zéro complexe i/2 du dénominateur. La preuve est indépendante d'une limitation de degré du multiplicateur. Associée aux deux cellules explicites, elle établit le contraste une cellule/deux cellules dans ce cadre précis de certificats. Elle ne démontre pas l'impossibilité de toutes les réalisations dynamiques.

## Portée scientifique

La compacité, les estimations de coefficients, les contractions, les séries de Neumann et la subdivision appartiennent à des méthodes classiques. La veille parallèle a identifié des antécédents de certification par subdivision et de représentations de Bernstein :

- Hamadneh, thèse 2018 : https://d-nb.info/1151075027/34
- Diniz, Salasar et Stern, *Positive Polynomials on closed boxes*, version 2, 2019 : https://arxiv.org/abs/1610.01437v2

Ces textes ne sont pas présentés comme énonçant exactement notre interface Lean. La différence de formulation n'établit pas une nouveauté. L'apport local est une frontière désormais formellement établie entre certificat global et atlas fini, avec raccord au checker du lab et exemples exacts.

Restent distincts : une couverture arbitraire non uniforme, l'optimalité générale des degrés ou du nombre de cellules, la complexité pratique, le recollement des états, la stabilité en cas de changement de cellule, et un système polynomial global unique. Aucun système biologique n'est étudié et aucune validation biologique n'est revendiquée.

## Restauration et validation

Lean 4.34.1 a été restauré depuis sa release officielle, avec vérification de l'empreinte de l'archive puis de celle du compilateur historique. Mathlib a été récupéré au commit exact attendu ; ses caches officiels ont été restaurés. Le premier essai de cache a échoué sur un dossier personnel en lecture seule, puis la configuration officielle vers un dossier de travail autorisé a réussi. Aucune protection n'a été supprimée.

Le paquet utilise 10 modules historiques du checker, recompilés sans modification, et 15 modules du présent lot, dont le module de norme complexe recopié sans modification de l'archive antérieure. Ce total n'est donc pas un décompte de théorèmes nouveaux. Il ne constitue pas une reconstruction de tout l'historique du lab ni de Mathlib depuis zéro.

L'audit porte sur **104 déclarations nommées de théorèmes et lemmes** du lot sélectionné et leurs dépendances transitives : seuls `propext`, `Classical.choice` et `Quot.sound` apparaissent. Les journaux et la liste exacte sont fournis. Aucun `sorry`, nouvel axiome ou `native_decide` ne sert aux preuves.

Une reconstruction du paquet portable a recompilé les 25 modules et reproduit l'audit. Une revue indépendante a de son côté reconstruit les 20 modules nécessaires à l'équivalence générale et au raccord checker, sans réutiliser les objets locaux de production, puis audité sept résultats centraux. Elle n'a pas recompilé les modules d'exemple `TwoCell*`. Les deux reconstructions réutilisent les dépendances Mathlib officielles ; elles ne reconstruisent pas toute Mathlib.

Trois sondes exécutables du checker produisent `true`, `4/3` et `1/4` pour l'acceptation, l'amplitude et la borne Lipschitz de l'exemple. Les identifiants et commits des dépendances restaurées ont été comparés au manifeste épinglé ; les détails figurent dans `verification/environment.json`.

Les sources du dernier paquet semantic-corona annoncé auparavant n'ont pas été retrouvées. Ce nouveau résultat part de l'archive corona effectivement restaurée ; il ne doit pas être présenté comme une reconstitution de ce dernier état manquant.
