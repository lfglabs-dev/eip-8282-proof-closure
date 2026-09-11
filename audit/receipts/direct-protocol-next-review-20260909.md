# Prochain pont formel : appels Θ, gas débité, budget cumulatif

Revue locale en lecture seule, 9 septembre 2026. Aucun build, changement de source ou vérification de nouvelle version du protocole. Les références externes restent celles du dossier et ne constituent pas un choix normatif de fork.

## Conclusion

Le prochain résultat autonome à prouver est **un append réellement réussi par Θ implique un débit positif de gas dans cette exécution**, puis sa somme sur une liste d'appels distincts. Cela fournit une vraie brique pour `BlockUsage.charged`, mais pas encore son instanciation protocolaire : l'affectation non dupliquée aux transactions, les refunds et la borne de bloc restent à démontrer.

En parallèle, une induction sur les états réellement produits est possible avec un budget cumulatif indépendant. Elle doit maintenir **excess + count ≤ budget en mode actif**, pas seulement les deux bornes séparées. Pour couvrir les états temporaires des appels imbriqués, le budget doit compter les appends de sous-appels réussis **y compris ceux annulés ultérieurement par un ancêtre**. Les appends finalement conservés sont un sous-ensemble ; leur nombre seul ne borne pas les états intermédiaires.

## Ce que donnent exactement les sources actuelles

- `ResourceBounds.BlockUsage` contient un slot et un gas de type `Fin (2^64)`, un nombre d'appends et une preuve fournie `appends ≤ gas.val`. `total_lt` en déduit `< 2^128` avec des slots distincts. `appendFits_of_accounted` suppose encore les bornes de tail/count observés ; il ne les dérive pas. `control_sum_fits` n'est pas une preuve de conservation de ces bornes.
- `ReachableCalls.Transition` lie réellement les mondes avant/après au résultat Θ, avec code installé et valeur apparente ordinaire. Les échecs restaurent le journal, et OutOfFuel ne crée pas une transition. Mais chaque appel choisit encore indépendamment gas, substate, originalWorld, header et caller. Aucun débit d'un budget commun ni lien à Υ ou à un bloc n'est présent.
- `ReachableCalls.From` est une proposition d'atteignabilité sans liste observable ni compteur. Il ne couvre que les appels au contrat épinglé. Ce n'est pas encore une trace de transaction générale avec wrappers et rollbacks d'ancêtres.
- `SuccessInversion.success_step` restitue le vrai résultat de `Z` et le vrai `StepOk`. `success_symBlock` conserve une égalité sur le fuel et rend le gas final existentiel ; il ne fournit pas encore une borne inférieure de consommation. Les bornes suffisantes `87*n+...` des théorèmes directs donnent assez de gas pour réussir, donc sont de la mauvaise direction pour prouver un coût minimal.
- `X` débite d'abord le coût mémoire, vérifie ensuite le coût d'opcode, puis `step` débite celui-ci. Les contrôles de `Z` permettent de justifier les soustractions naturelles, sans sous-flux UInt256. Les preuves génériques de monotonie doivent exclure les opérations CALL/CREATE ou traiter leurs retours de gas : cette exclusion doit être dérivée du chemin des runtimes audités, pas postulée pour un programme arbitraire.

## Premier livrable recommandé : ActualAppendGas

1. Extraire de `Z vj op pre = .ok (mid,cost)` les inégalités et égalités naturelles suivantes : coût mémoire ≤ gas initial ; gas intermédiaire = gas initial moins coût mémoire ; coût opcode ≤ gas intermédiaire. Employer les lemmes `toNat_sub_ofNat` avec ces inégalités dérivées.
2. Pour les opcodes ordinaires des chemins épinglés, ajouter à l'inversion de pas l'égalité `postGas + memoryCost + opcodeCost = preGas`, en Nat. Garder la preuve attachée à `Z` et `StepOk` réels. Renforcer la composition de blocs et de boucles avec une consommation accumulée, sans remplacer l'interpréteur.
3. Par inversion du vrai chemin append, identifier le LOG0 effectivement exécuté et la taille de son record. `C'` lui facture `375 + 8*len` : 1847 gas pour 184 octets de dépôt, 919 pour 68 octets de sortie, avant coût mémoire. Ces nombres proviennent du gas de la sémantique épinglée, pas d'une mesure Anvil.
4. Télescoper les égalités de gas sur le chemin, où aucun opcode ne rend du gas à cette frame. Avec l'inversion Θ→Ξ déjà disponible, viser par exemple :

   `actual Θ success ∧ pinned runtime ∧ non-SYSTEM ∧ nonempty calldata`
   `→ finalGas.toNat + logCost(kind) ≤ call.gas.toNat`.

   La classification de calldata doit être dérivée de l'admission avec la borne d'encodage de taille explicite. Aucune hypothèse `AppendFits`, de post-stockage, de budget de bloc ou de borne suffisante de gas ne doit être nécessaire à ce seul résultat de coût.
5. Une première composition sur une liste de véritables résultats Θ donne `919 * appendCount ≤ Σ(inputGas - outputGas)` pour les appels sélectionnés distincts. C'est un théorème de liste d'appels, pas encore un théorème sur le gasUsed du bloc. Ne pas supposer son membre droit égal à un compteur de bloc.

Les inversions de pas et la classification utilisateur existantes rendent ce travail local crédible. L'inversion complète de suffixe append doit être disponible pour chaque runtime ; au moment de la lecture, le nouveau `AppendInversion` expose surtout la chaîne complète exit, tandis que deposit et SYSTEM demandent encore leur classification complète avant une induction couvrant tous les résultats. Ce constat concerne les fichiers observés, pas les travaux parallèles ultérieurs.

## Deuxième livrable : induction d'état à budget explicite, sans circularité

Ajouter une trace concrète indexée par le nombre d'événements, ou une liste dépendante de transitions réelles, avec un oubli vers `ReachableCalls.From`. Définir le poids d'un appel par ses entrées et son statut réel : succès, caller non-SYSTEM, calldata non vide. Prouver ensuite, grâce à l'admission et à l'inversion de suffixe, que ce poids correspond à exactement un append. Ne pas définir le poids comme « la postcondition souhaitée est vraie ».

Pour un état observé au budget A, l'invariant utile est :

- `HEAD ≤ TAIL ≤ A` et `count ≤ A` ;
- si slot0 ≠ INHIBITOR, `excess + count ≤ A` ;
- initialement les quatre contrôles sont ceux de l'installation justifiée, avec A=0 pour les contrôles nuls ; exit peut initialement être inhibé.

Avec une borne indépendante A ≤ B et B < 2^128, dériver `AppendFits` **avant** de lire le post-append. Les lemmes indépendants de stockage permettent alors de prouver les successeurs naturels de count/tail. Sur SYSTEM, le reset de count, le latch, l'unlock et le fold conservent l'invariant ; la somme couplée donne directement le non-débordement nécessaire. Les bornes séparées `excess≤A` et `count≤A` ne suffisent pas seules : leur somme peut être 2A.

Les getters et les échecs conservent les observations, par inversion du résultat réel. Les ressources suffisantes des théorèmes forward ne doivent pas être ajoutées pour éliminer arbitrairement des succès à plus faible gas : utiliser une inversion SYSTEM/append complète ou annoncer explicitement un domaine restreint.

Pour les wrappers, l'induction doit voir le vrai journal : un append local augmente le budget monotone, puis un rollback d'ancêtre restaure un ancien état qui satisfaisait déjà une borne plus petite. Ne pas diminuer le budget à ce rollback. Il faut enrichir l'extraction de trace pour inclure cette restauration réelle et les étapes externes qui préservent le stockage du contrat. La relation `From` actuelle ne peut pas représenter seule une telle transaction générale.

## Troisième livrable : comptabilité transactionnelle puis bloc

Les obligations ne peuvent pas être remplacées par le seul coût positif de LOG0 :

1. **Pas de double comptage.** Associer chaque append à une occurrence unique de sous-appel dans l'arbre d'exécution. Les runtimes audités ne font pas eux-mêmes d'appel sortant, ce qui simplifie les occurrences sélectionnées, mais un wrapper peut en appeler plusieurs. Sommer les consommations des frames parentes et filles doublerait le coût des filles. Prouver un bilan de gas sur l'arbre réel, incluant CALL, les retours de gas et le stipend. Dans le code actuel, `Ccallgas` peut ajouter 2300 alors que `Ccall` facture le cap et les frais de transfert : une simple inégalité « gas transféré ≤ gas réservé » serait fausse sans traiter ce détail.
2. **Gross versus net.** Dans Υ, `gStar = g' + min ((gasLimit-g')/5) refundBalance`, puis le gasUsed retourné est `gasLimit-gStar`, en UInt256. Il faut lier ces mots à des Nat sans wrap à partir de transaction valide et de `g'≤gasLimit`. Pour gross=`gasLimit-g'`, montrer refund≤floor(gross/5) puis net≥gross-floor(gross/5). Le coût minimal 919 par événement laisse largement assez de marge pour déduire événements≤net. Un résultat seulement `1≤gross` par événement ne suffit pas en général après refunds.
3. **Validation réelle.** Υ suppose dans son commentaire que la transaction est déjà valide ; il ne prouve pas cette admission. Il faut notamment borner gasLimit, justifier intrinsicGas≤gasLimit, lier le code exécuté à l'account installé, et le gas de chaque sous-appel à son parent. Un `Context.gas : UInt256` arbitraire ne fournit aucun budget 64 bits.
4. **Monde final de transaction.** Après Θ, Υ ajuste les balances, traite selfDestructSet/deadAccounts et efface le stockage transitoire. Pour transporter l'invariant d'un appel au prochain, prouver que ces étapes et les opérations externes ne suppriment ni ne remplacent le code/stockage audité dans le domaine retenu. Les sous-états arbitraires autorisés par `From` ne fournissent pas cette garantie.
5. **Bloc et histoire.** Lier la somme des gasUsed des transactions à un unique payload gasUsed borné, puis ce payload à un slot canonique distinct. Les appels SYSTEM hors gasUsed transactionnel ne créent pas d'appends dans le modèle de dispatch, mais leur placement, autorisation et éventuels chemins d'activation restent à lier.

Après ces preuves seulement, construire `BlockUsage.charged` à partir des traces, et appliquer `ResourceBounds.total_lt` puis l'induction d'état. On peut utiliser le nombre d'événements localement réussis, même annulés ensuite : son majorant facture précisément du travail exécuté, et majore aussi les appends finaux conservés.

## Choix de domaine indispensables

Aucun théorème sur tous les `Context` Θ actuels ne peut conclure une borne cumulative protocolaire : ils autorisent une nouvelle dotation en gas à chaque appel, des headers Nat arbitraires et un caller SYSTEM choisi librement. Il faut annoncer le protocole/fork, les règles de slots/payloads, l'initialisation/activation, les mises à niveau permises et le traitement des appels imbriqués.

Un premier jalon limité aux transactions top-level ordinaires directement adressées au contrat serait raisonnable pour développer le pont Υ ; il ne clôturerait pas les garanties promises pour les appels imbriqués. Ne pas le présenter comme le domaine Ethereum entier.

Enfin, `<2^128` appends protège les adresses de stockage et les additions de contrôle, **pas** les produits de la récurrence tarifaire. `FundedDomain` garde un plafond de valeur externe explicite ; sa justification économique et la décision sur le tarif mathématique restent des obligations distinctes. Elles ne découlent ni du coût d'un opcode ni du nombre fini de slots.

## Empreintes des sources principales lues

- `audit/PROTOCOL-BOUNDARY.md`: `634d85b40da80622d1fc69e99ce27796c6d718ea8de348268549e762e210a258`
- `Integrator/ResourceBounds.lean`: `099a06b7178531f58fb8c889ecd583bbe7fd890d1490ae0261d971f5640d87b6`
- `Integrator/ReachableCalls.lean`: `6faeb4ce64325ccd5bf0c9314a89e158382b479e59df59b3dd531b221208f585`
- `Integrator/SuccessInversion.lean`: `16296f56350ba53322d29e8cce6c8799ae95c175489d92689ed170d2875297c7`
- pinned `EVM/Semantics.lean`: `8b49f1aee609ce888041ba9e7253bbe55d06fda136252bc46d4e006755110f4b`
- pinned `EVM/Gas.lean`: `9f06caccf5cc8f27f7822392cd1963c8353eb816052f4596321a12c2da707436`
