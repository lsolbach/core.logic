;   Copyright (c) David Nolen, Rich Hickey, contributors. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns clojure.core.logic.dcg
  "Definite Clause Grammars"
  (:refer-clojure :exclude [==])
  (:require [clojure.core.logic :as l]))

;; TODO: think about indexing
;; TODO: note that rest args are problematic since we add two invisible args
;; TODO: make handle-clause polymorphic, we don't want to futz around with
;; with forcing macroexpand
;; TODO: fresh-expr? and !dcg? are odd, why can't we check w/ `sym

(defn lsym [n]
  (gensym (str "l" n "_")))

(defn !dcg? [clause]
  (and (sequential? clause)
       (let [f (first clause)]
         (and (symbol? f)
              (= (name f) "!dcg")))))
 
(defn ->lcons
  ([env [m :as c] i] (->lcons env c i false))
  ([env [m :as c] i quoted]
     (cond
      (empty? c) `(l/fresh []
                    (l/== ~(env (dec i)) ~(env i)))
      :else (let [m (if quoted `(quote ~m) m)]
              `(l/== ~(env (dec i)) (l/lcons ~m ~(env i)))))))

(defn fresh-expr? [clause]
  (and (seq? clause)
       (let [f (first clause)]
         (and (symbol? f)
              (= (name f) "fresh")))))

;; TODO: make tail recursive

(defn count-clauses [clauses]
  (if (fresh-expr? clauses)
    (count-clauses (drop 2 clauses))
    (reduce (fn [s c]
              (cond
               (fresh-expr? c) (+ s (count-clauses (drop 2 c)))
               (!dcg? c) s
               :else (clojure.core/inc s)))
            0 clauses)))

;; TODO: might as well make this a lazy-seq

(defn mark-clauses
  ([cs] (mark-clauses cs (atom 0)))
  ([[c & r :as cs] i]
     (cond
      (nil? (seq cs)) ()
      (fresh-expr? c) (cons `(l/fresh ~(second c)
                          ~@(mark-clauses (drop 2 c) i))
                       (mark-clauses r i))
      (!dcg? c) (cons c (mark-clauses r i))
      :else (cons (with-meta c
                    {:index (swap! i clojure.core/inc)})
                  (mark-clauses r i)))))

;; TODO: same as above
;; combine this step with the above

(defn handle-clauses [env [c & r :as cs]]
  (cond
   (nil? (seq cs)) ()
   (fresh-expr? c) (cons `(l/fresh ~(second c)
                       ~@(handle-clauses env (drop 2 c)))
                    (handle-clauses env r))
   (!dcg? c) (cons (second c) (handle-clauses env r))
   (vector? c) (cons (->lcons env c (-> c meta :index))
                     (handle-clauses env r))
   (and (seq? c)
        (= (first c) `quote)
        (vector? (second c))) (cons (->lcons env (second c) (-> c meta :index) true)
                                     (handle-clauses env r))
   :else (let [i (-> c meta :index)
               c (if (seq? c) c (list c))]
           (cons (concat c [(env (dec i)) (env i)])
                 (handle-clauses env r)))))

(defmacro --> [name & clauses]
  (let [r (range 1 (+ (count-clauses clauses) 2))
        lsyms (into [] (map lsym r))
        clauses (mark-clauses clauses)
        clauses (handle-clauses lsyms clauses)]
    `(defn ~name [~(first lsyms) ~(last lsyms)]
       (l/fresh [~@(butlast (rest lsyms))]
         ~@clauses))))

(defmacro def--> [name args & clauses]
  (let [r (range 1 (+ (count-clauses clauses) 2))
        lsyms (map lsym r)
        clauses (mark-clauses clauses)
        clauses (handle-clauses lsyms clauses)]
   `(defn ~name [~@args ~(first lsyms) ~(last lsyms)]
      (l/fresh [~@(butlast (rest lsyms))]
        ~@clauses))))

(defn handle-cclause [fsym osym cclause]
  (let [c (count-clauses cclause)
        r (range 2 (clojure.core/inc c))
        lsyms (conj (into [fsym] (map lsym r)) osym)
        clauses (mark-clauses cclause)
        clauses (handle-clauses lsyms clauses)]
    `(l/fresh [~@(butlast (rest lsyms))]
       ~@clauses)))

(defmacro -->e [name & cclauses]
  (let [fsym (gensym "l1_")
        osym (gensym "o")]
   `(defn ~name [~fsym ~osym]
      (l/conde
       ~@(map list (map (partial handle-cclause fsym osym) cclauses))))))

(defmacro def-->e [name args & pcss]
  (let [fsym (gensym "l1_")
        osym (gensym "o")]
   `(l/defne ~name [~@args ~fsym ~osym]
      ~@(map (fn [[p & cs]]
               (list (-> p (conj '_) (conj '_))
                     (handle-cclause fsym osym cs)))
             pcss))))

(comment
  (-->e det
    ('[the])
    ('[a]))
  
  (-->e n
    ('[witch])
    ('[wizard]))

  (--> v '[curses])

  (--> np det n)
  (--> vp v np)
  (--> s np vp)

  ;; we can stop the dcg transform
  (--> s np (!dcg (l/== 1 1)) vp)

  ;; success
  (l/run* [q]
    (np '[the witch] []))

  ;; success
  (l/run* [q]
    (s '[a witch curses the wizard] []))

  (def-->e verb [v]
    ([[:v 'eats]] '[eats]))

  (def-->e noun [n]
    ([[:n 'bat]] '[bat])
    ([[:n 'cat]] '[cat]))

  (def-->e det [d]
    ([[:d 'the]] '[the])
    ([[:d 'a]] '[a]))

  (def-->e noun-phrase [n]
    ([[:np ?d ?n]] (det ?d) (noun ?n)))
  
  (def-->e verb-phrase [n]
    ([[:vp ?v ?np]] (verb ?v) (noun-phrase ?np)))

  (def-->e sentence [s]
    ([[:s ?np ?vp]] (noun-phrase ?np) (verb-phrase ?vp)))

  (l/run 1 [parse-tree]
    (sentence parse-tree '[the bat eats a cat] []))

  ;; ([:s [:np [:d the] [:n bat]] [:vp [:v eats] [:np [:d a] [:n cat]]]])

  ;; ~90-100ms
  (dotimes [_ 10]
    (time
     (dotimes [_ 1e3]
       (l/run 1 [parse-tree]
         (sentence parse-tree '[the bat eats a cat] [])))))

  ;; parsing lisp

  (def digits (into #{} "1234567890"))
  (defn cr [c1 c2]
    (map char (range (int c1) (int c2))))
  (def alpha (into #{} (concat (cr \a \z) (cr \A \Z))))
  (def alnum (into digits (concat (cr \a \z) (cr \A \Z))))
  (def nonalnum (into #{} "+/-*><="))
  
  (-->e wso
    ([\space] wso)
    ([]))

  (def-->e digito [x]
    ([_] [x]
       (!dcg
        (l/project [x]
          (l/== (contains? digits x) true)))))

  (def-->e numo [x]
    ([[?d . ?ds]] (digito ?d) (numo ?ds))
    ([[?d]] (digito ?d)))

  (declare symro)
  
  (def-->e symo [x]
    ([[?a . ?as]] [?a]
       (!dcg
        (l/project [?a]
          (l/conde
            ((l/== (contains? alpha ?a) true))
            ((l/== (contains? nonalnum ?a) true)))))
       (symro ?as)))

  (def-->e symro [x]
    ([[?a . ?as]] [?a]
       (!dcg
        (l/project [?a]
          (l/conde
            ((l/== (contains? alnum ?a) true))
            ((l/== (contains? nonalnum ?a) true)))))
       (symro ?as))
    ([[]] []))

  (declare exprso)

  (def-->e expro [e]
    ([[:sym ?a]] (symo ?a))
    ([[:num ?n]] (numo ?n))
    ([[:list ?list]] [\(] (exprso ?list) [\)])
    ([[:sym :quote ?q]] [\'] (expro ?q)))

  ;; TODO: we need cut here, we found a valid parse
  (def-->e exprso [exs]
    ([[?e . ?es]] wso (expro ?e) wso (exprso ?es))
    ([[]] []))

  ;; (_.0)
  (l/run* [q]
    (wso (vec "  ") []))

  ;; ()
  (l/run* [q]
    (wso (vec " f ") []))

  ;; (\1)
  (l/run* [q]
    (digito q [\1] []))

  ;; ((\1 \2 \3))
  (l/run* [q]
    (numo q (vec "123") []))

  ;; ((\a \b \c))
  (l/run* [q]
    (symo q (vec "abc") []))

  ;; ([:n (\1 \2 \3)])
  (l/run* [q]
    (expro q (vec "123") []))

  ;; ([:s (\a \b \c)])
  (l/run* [q]
    (expro q (vec "abc") []))

  ;; (([:list ([:sym (\+)] [:sym (\a \b \c)] [:sym (\b)] [:sym :quote [:list ([:num [\1]] [:num (\2 \3)])]])]))
  (l/run 1 [q]
    (exprso q (vec " (+ abc b '(1 23))  ") []))

  ;; w/ def-->a ~2500ms
  ;; w/ def-->e ~1400ms
  (dotimes [_ 10]
    (let [s (vec " (+ abc b '(1 23))  ")]
      (time
       (dotimes [_ 50]
         (l/run 1 [q]
           (exprso q s []))))))
  )
