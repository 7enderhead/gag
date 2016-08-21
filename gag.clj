(ns gag
  (:require [clojure.set :refer [subset?]]
            [clojure.test :refer [is]]))

(defmacro is!
  "Generates a version of clojure.test/is that throws an
  AssertionError when the assertion fails."
  ([form]
   `(is! ~form nil))
  ([form msg]
   `(when (not (is ~form ~msg)) (throw (AssertionError.)))))

(set! *print-length* 100)
(set! *print-level* 10)

;;; Tapes

(defrecord Tape
  [;; blank symbol used as default value for yet unvisited tape positions
   blank
   ;; sequence of already manipulated symbols before head position
   ;; first element is first symbol before head
   pre
   ;; symbol at head position
   head 
   ;; sequence of already manipulated symbols after head position
   ;; first element is first symbol after head
   post
   ])

(defn make-tape
  ([]
  "New tape with default blank symbol"
   (make-tape \.))
  ([blank]
   "New tape with given blank symbol"
   (->Tape blank '() blank '()))
  ([pre head post & blank]
   (let [blank (if blank blank \.)]
     (->Tape blank (reverse (seq pre)) head (seq post)))))

(defn blankify
  [tape part]
  "Append infinite seq of blank symbol to tape 'part'"
  (concat (part tape) (repeat (:blank tape))))

(defn- take-context
  [tape part context]
  "Take 'context' symbols from tape part 'part'"
  (take context (blankify tape part)))

(defn pprint-tape
  ([tape]
   "Print complete tape contents, i.e., cells that have already been
   writte to: pre[head]post"
   (pprint-tape tape (:pre tape) (:post tape)))
  ([tape context]
   "Print tape content with context number of symbols in either direction of head:
   pre[head]post"
   (pprint-tape tape
                (take-context tape :pre context)
                (take-context tape :post context)))
  ([tape pre post]
   (str "#gag.Tape{"
        (apply str (->> pre (reverse)))
        "[" (:head tape) "]"
        (apply str post)
        "}"))) 

(defmethod print-method Tape
  [tape ^java.io.Writer writer]
  (.write writer (pprint-tape tape)))

(defmethod print-dup Tape
  [tape ^java.io.Writer writer]
  (print-method tape writer))

;;; Actions on Tapes

(defrecord Tape-Action [write move])

(defn make-tape-action
  [write move]
  {:pre [(is (contains? #{:left, :right, :stay} move))]}
  (->Tape-Action write move))

(defn- first-or-default
  [s default]
  "First element of seq 's' or 'default' if no element"
  (if-let [frst (first s)]
    frst
    default)) 

(defn- tape-first
  [tape part]
  "First symbol from tape part"
  (first-or-default (part tape) (:blank tape)))

(defmulti act-tape 
  "Perform given action on tape"
  (fn [tape action] (:move action)))

(defmethod act-tape :stay
  [tape action]
  (assoc tape :head (:write action)))

(defmethod act-tape :left
  [tape action]
  (assoc tape
         :head (tape-first tape :pre)
         :pre (rest (:pre tape))
         :post (cons (:write action) (:post tape))))

(defmethod act-tape :right
  [tape action]
  (assoc tape
         :head (tape-first tape :post)
         :pre (cons (:write action) (:pre tape))
         :post (rest (:post tape))))


;;; Transitions for a Complete Machine

(defprotocol Arity 
  (arity [x]))

(extend-type nil
  Arity
  (arity [_] 0))

(defrecord Transition [state symbols next-state tape-actions]
  Arity
  (arity [transition] (count (:symbols transition))))

(defn- vectorify
  "Put x into a vector if it isn't one already."
  [x]
  (if (vector? x)
    x
    [x])) 

(defn make-transition
  [state symbols next-state actions]
  (let [symbols (vectorify symbols)
        actions (vectorify actions)
        actions (if (every? #(instance? Tape-Action %) actions)
                  actions
                  ;; convenience: create Tape-Actions from parameter pairs
                  ;; nil padding ensures correct number of parameters (move cannot be nil)
                  (into [] (map #(apply make-tape-action %) (partition 2 2 nil actions))))]
    (is! (= (count symbols) (count actions)))
    (->Transition state
                  symbols
                  next-state
                  actions)))

(defn valid-transition?
  [transition states tape-alphabet input-alphabet]
  (is! (contains? states (:state transition)) "state")
  (is! (contains? states (:next-state transition)) "next state")
  (is! (every? #(contains? tape-alphabet %) (:symbols transition)) "transition symbol")
  (is! (every? #(contains? tape-alphabet (:write %)) (:tape-actions transition)) "transition write symbol")
  true)

;;; Machines

(defrecord Machine-Definition [states
                               initial-state
                               final-states
                               tape-alphabet
                               input-alphabet
                               blank-symbol
                               transitions]
  Arity
  (arity [machine-definition] 
    (-> (:transitions machine-definition)
        (first)
        (arity))))

(defn make-machine-definition
  [states initial-state final-states tape-alphabet input-alphabet blank-symbol transitions]
  {:pre [(is (set? states))
         (is (contains? states initial-state))
         (is (or (set? tape-alphabet) (string? tape-alphabet)))
         (is (or (set? input-alphabet) (string? input-alphabet)))]}
  (let [final-states (if (set? final-states) final-states #{final-states})
        tape-alphabet (set tape-alphabet)
        input-alphabet (set input-alphabet)]
    (is! (subset? final-states states))
    (is! (subset? input-alphabet tape-alphabet))
    (is! (not (contains? input-alphabet blank-symbol)))
    (is! (every? #(valid-transition? % states tape-alphabet input-alphabet) transitions))  
    (is! (<= (count (into #{} (map arity transitions))) 1) "transitions all same arity")
    (->Machine-Definition states
                          initial-state
                          final-states
                          tape-alphabet
                          input-alphabet
                          blank-symbol
                          transitions)))

;; Machine configuration: current program state and 1 to n tapes
(defrecord Configuration [;; [step-number unique-position]
                          id
                          ;; see id
                          parent-id
                          state
                          tapes]
  Arity
  (arity [configuration] (count (:tapes configuration))))

(defn make-configuration
  [id parent-id state tapes]
  (let [tapes (vectorify tapes)]
    (->Configuration id parent-id state tapes)))

(defprotocol Machine-Access
  (initialize [machine tapes])
  (configurations [machine])
  (perform-step [machine])
  )

(defn current-step 
  [machine] 
  (dec (count (configurations machine))))

(defn current-configurations 
  [machine] (last (configurations machine)))

(defn apply-transitions
  "Apply corresponding transitions to configuration, producing a sequence of one or
  more new configurations. Transitions are grouped by {:state :symbols}"
  [configuration all-transitions]
  (let [symbols (into [] (map :head (:tapes configuration)))
        transitions (filter 
                      (fn [[k v]]
                        (and (= (:state configuration) (:state k))
                             (= symbols (:symbols k))))
                      all-transitions)])
  )

(defn grouped-transitions
  "Group transitions by {:state :symbols} for easy mapping
  to configurations where they apply."
  [machine]
  (->> (get-in machine [:definition :transitions])
       ((group-by #(select-keys % [:state :symbols])))))

(defrecord Machine [;; Machine-Definition
                    definition
                    ;; Nested vector of configurations
                    ;; Outer level is step number
                    ;; Step 0 is initial configuration, i.e., input
                    configurations]
  Machine-Access
  (initialize [machine tapes]
    (assoc machine :configurations
           (conj (:configurations machine)
                 (make-configuration [0 0] nil (:initial-state (:definition machine)) tapes))))
  (configurations [machine] (:configurations machine))
  (perform-step
    [machine]
    (let [grouped (grouped-transitions machine)
          new-configurations (map #(apply-transitions % grouped)
                                  (current-configurations machine))]

      )))

(defn make-machine
  [definition input-tapes]
  (let [tapes (vectorify input-tapes)] 
    (is! (= (arity definition) (count (vectorify tapes))))
    (is! (every? #(= (:blank-symbol definition) (:blank %)) tapes))
    (-> (->Machine definition [])
        (initialize input-tapes))))
