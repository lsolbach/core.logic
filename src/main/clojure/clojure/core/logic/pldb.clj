;   Copyright (c) David Nolen, Rich Hickey, contributors. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns clojure.core.logic.pldb
  "A persistent core.logic database.
   The goal of pldb is to provide core.logic fact/relation mechanism that doesn't use mutable namespace references.
   This makes it easier to use core.logic in multi-threaded environments like web applications."
  (:refer-clojure :exclude [indexed?])
  (:require [clojure.core.logic :as l]))

;; ----------------------------------------

(def empty-db {})

(defmacro with-dbs
  "Creates bindings for the given `dbs` and executes the `body` in the context of these bindings."
  [dbs & body]
  `(binding [l/*logic-dbs* (concat l/*logic-dbs* ~dbs)]
          ~@body))

(defmacro with-db
  "Creates a binding for the given `db` and executes the `body` in the context of this binding."
  [db & body]
  `(binding [l/*logic-dbs* (conj l/*logic-dbs* ~db)]
          ~@body))

(defn facts-for
  "Returns the facts from the `dbs` with the key `kname`."
  [dbs kname]
  (mapcat #(get-in % [kname ::unindexed]) dbs))

(defn facts-using-index
  "Returns the facts from the `dbs` with the key `kname` using the `index` and `val` for lookup."
  [dbs kname index val]
  (mapcat #(get-in % [kname index val]) dbs))

;; ----------------------------------------
(defn rel-key
  "Returns the key for the relation `rel`."
  [rel]
  (if (keyword? rel)
    rel
    (:rel-name (meta rel))))

(defn rel-indexes
  "Returns the indexes defined on the relation `rel`."
  [rel]
  (:indexes (meta rel)))

(defn indexed?
  "Returns true if `v` is indexed."
  [v]
  (true? (:index (meta v))))


(defn contains-lvar?
  "Returns true if `x` contains logic variables (lvars)."
  [x]
  (some l/lvar? (tree-seq coll? seq x)))

(defn ground?
  "Returns true if `x` contains logic variables (lvars)."
  [s term]
  (not (contains-lvar? (l/walk* s term))))

(defn index-for-query
  [s q indexes]
  (let [indexable (map #(ground? s %)  q)
        triples (map vector (range) indexable indexes)]
    (first (for [[i indexable indexed] triples
                 :when (and indexable indexed)]
             i))))

(defmacro db-rel
  "Refines a relation with `name` and the given `args`."
  [name & args]
  (let [arity
        (count args)

        kname
        (str (ns-name *ns*) "/" name "_" arity)

        indexes
        (vec (map indexed? args))]
    `(def ~name
       (with-meta
         (fn [& query#]
           (fn [subs#]
             (let [dbs#
                   (-> subs# clojure.core/meta :db)

                   facts#
                   (if-let [index# (index-for-query subs# query# ~indexes)]
                     (facts-using-index dbs#
                                        ~kname
                                        index#
                                        (l/walk* subs# (nth query# index#)))
                     (facts-for dbs# ~kname))]
               (l/to-stream (map (fn [potential#]
                                   ((l/== query# potential#) subs#))
                                 facts#)))))
         {:rel-name ~kname
          :indexes ~indexes}))))

;; ----------------------------------------

(defn db-fact
  "Returns a new db by adding to the given `db` the fact of relation `rel` with the `args`."
  [db rel & args]
  (let [key
        (rel-key rel)

        add-to-set
        (fn [current new]
          (conj (or current #{}) new))

        db-with-fact
        (update-in db [key ::unindexed] #(add-to-set %1 args))

        indexes-to-update ;; ugly - get the vector indexes of indexed attributes
        (map vector (rel-indexes rel) (range) args)

        update-index-fn
        (fn [db [is-indexed index-num val]]
          (if is-indexed
            (update-in db [key index-num val] #(add-to-set %1 args))
            db))]
    (reduce update-index-fn db-with-fact indexes-to-update)))

(defn db-retraction
  "Retracts the relation `rel` from the database `db`."
  [db rel & args]
  (let [key
        (rel-key rel)

        retract-args
        #(disj %1 args)

        db-without-fact
        (update-in db [key ::unindexed] retract-args)

        indexes-to-update ;; also a bit ugly
        (map vector (rel-indexes rel) (range) args)

        remove-from-index-fn
        (fn [db [is-indexed index-num val]]
          (if is-indexed
            (update-in db [key index-num val] retract-args)
            db))]

    (reduce remove-from-index-fn db-without-fact indexes-to-update)))

;; ----------------------------------------
(defn db-facts
  "Returns a facts database based on `base-db` with the given `facts` added."
  [base-db & facts]
  (reduce #(apply db-fact %1 %2) base-db facts))

(defn db
  "Returns a new facts database with the given `facts` added."
  [& facts]
  (apply db-facts empty-db facts))

(defn db-retractions
  "Returns a database based on `base-db` with the given `retractions` removed."
  [base-db & retractions]
  (reduce #(apply db-retraction %1 %2) base-db retractions))

