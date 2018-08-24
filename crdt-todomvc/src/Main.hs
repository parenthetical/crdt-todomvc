{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings, RecursiveDo, ScopedTypeVariables, FlexibleContexts, TypeFamilies
, ConstraintKinds
, LambdaCase
, NamedFieldPuns
#-}
{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE NoMonomorphismRestriction, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, TypeFamilies, FlexibleContexts, DeriveDataTypeable, GeneralizedNewtypeDeriving, StandaloneDeriving, ConstraintKinds, UndecidableInstances, PolyKinds, AllowAmbiguousTypes #-}


-- Copyright (c) 2016, Ryan Trinkle

-- All rights reserved.

-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions are met:

--     * Redistributions of source code must retain the above copyright
--       notice, this list of conditions and the following disclaimer.

--     * Redistributions in binary form must reproduce the above
--       copyright notice, this list of conditions and the following
--       disclaimer in the documentation and/or other materials provided
--       with the distribution.

--     * Neither the name of Doug Beardsley nor the names of other
--       contributors may be used to endorse or promote products derived
--       from this software without specific prior written permission.

-- THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
-- "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
-- LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
-- A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
-- OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
-- SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
-- LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
-- DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
-- THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
-- (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
-- OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

import Prelude hiding (mapM, mapM_, all, sequence)
import Control.Monad.Fix
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Foldable
import Data.Monoid ((<>))
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.List as List
import Data.Text.Encoding (encodeUtf8)
import Control.Lens ((^.))
import Control.Monad.IO.Class
import Text.Read (readMaybe)
import Data.Maybe (fromJust)
import qualified Crdt as C
import Crdt (Crdt)
import Reflex
import Reflex.Dom
import qualified GHCJS.DOM.GlobalEventHandlers as GEH
import qualified GHCJS.DOM.HTMLInputElement as IE
import GHCJS.DOM.EventM
import GHCJS.DOM.Types (unsafeCastTo,Element(..))
import GHC.IORef (IORef(..))
import qualified GHCJS.DOM.KeyboardEvent as KE
import qualified Crdt.Local as CD
import Language.Javascript.JSaddle


--------------------------------------------------------------------------------
-- Model
--------------------------------------------------------------------------------

type Task = (Bool, String)
taskCompleted :: Task -> Bool
taskCompleted = fst
taskDescription :: Task -> String
taskDescription = snd
type Tasks = Map TaskId Task
type I = Int
type TaskId = CD.Id
type Op = [ ( Maybe TaskId
            , TaskOp
            )
          ]

type TaskOp =
  [C.Clearable (Either Bool (C.SeqOp Char))]

todoCrdt :: Crdt TaskId Op Tasks
todoCrdt =
 C.concurrent
  (C.iddict (const True)
   (C.concurrent (
      C.clrSome (
          C.pair
            C.dwflag
            (C.mutableSequence C.constValUnsafe)))))

newTask :: String -> Op
newTask description =
  [(Nothing, [C.Do (Right (C.SeqReplace description))])]

setCompleted :: Bool -> TaskOp
setCompleted c = [C.Do (Left c)]

changeDescription :: (Int, C.SeqIdxOp Char) -> TaskOp
changeDescription op = [C.Do (Right (uncurry C.SeqIdx $ op))]

clearCompleted :: Tasks -> Op
clearCompleted tasks =
  map (\tid -> (Just tid, destroy))
  . Map.keys
  . Map.filter taskCompleted
  $ tasks

toggleCompleted :: Bool -> Tasks -> Op
toggleCompleted c tasks =
  map (\(tid,_task) -> (Just tid, setCompleted c))
  $ Map.toList tasks

destroy :: TaskOp
destroy = [C.Clear]

--------------------------------------------------------------------------------
-- Filters
--------------------------------------------------------------------------------

-- | Subsets of the task list that can be selected by the user
data Filter
   = All -- ^ All tasks
   | Active -- ^ Uncompleted tasks
   | Completed -- ^ Completed tasks
   deriving (Show, Eq)


-- | Determine whether this Task should be shown when this Filter is in effect
satisfiesFilter :: Filter -> Task -> Bool
satisfiesFilter f = case f of
  All -> const True
  Active -> not . taskCompleted
  Completed -> taskCompleted

--------------------------------------------------------------------------------
-- Local storage
--------------------------------------------------------------------------------

save :: (Show state) => String -> state -> JSM ()
save wher state = do
  _ <- jsg ("window" :: Text)
       ^. js ("localStorage" :: Text)
       ^. jsf ("setItem" :: Text) (wher,show state)
  return ()

load :: (Read state,Show state) => String -> state -> JSM state
load wher initVal = do
  jsv <- jsg ("window" :: Text)
         ^. js ("localStorage" :: Text)
         ^. jsf ("getItem" :: Text) [wher]
  liftJSM (maybe initVal id
           . readMaybe
           . fromJust
           <$> fromJSVal jsv)

reset :: String -> JSM ()
reset wher = do
  _ <- jsg ("window" :: Text)
       ^. js ("localStorage" :: Text)
       ^. jsf ("removeItem" :: Text) [wher]
  return ()


-- --------------------------------------------------------------------------------
-- -- View
-- --------------------------------------------------------------------------------
main :: IO ()
main = mainWidgetWithCss (encodeUtf8 css) todoMVC

todoMVC :: (MonadWidget t m) => m ()
todoMVC = do
  let CD.Local initState applyOp evalState =
        CD.compile todoCrdt
  start <- liftJSM $ load "state" initState
--  let (i,start) = (iMaybeNew,initAlgoState)
  ctx <- unJSContextSingleton <$> askJSContext
  el "div" $ do
    elAttr "section" ("class" =: "todoapp") $ do
      mainHeader
      rec
        -- FIXME Needs to fall back to good state if no parse.
        tasksDyn <-
          foldDyn (\op state -> applyOp state op) start allOps
        let tasksE = --traceEvent "State"
              (updated tasksDyn)
        performEvent_ . ffor tasksE $
          liftIO . runJSaddle ctx . save "state"
        let tasks' = traceDyn "CRDT state" (evalState <$> tasksDyn)
        newTaskE <- taskEntry
        listModifyTasksE <-
          taskList activeFilter -- activeFilter
          tasks'
        (activeFilter, clearCompletedE) <- controls tasks'
        let allOps =
              traceEvent "Ops"
              (newTaskE <> listModifyTasksE <> clearCompletedE)
        return ()
      infoFooter
    resetE <- button "Reset"
    performEvent_ $ (liftIO . runJSaddle ctx $ reset "state") <$ resetE

-- | Display the main header
mainHeader :: DomBuilder t m => m ()
mainHeader = el "h1" $ text "todos"

-- | Strip leading and trailing whitespace from the user's entry, and
-- discard it if nothing remains
stripDescription :: T.Text -> Maybe T.Text
stripDescription d =
  let trimmed = T.strip d
  in if T.null trimmed
     then Nothing
     else Just trimmed

-- | Display an input field; produce new Tasks when the user creates them
taskEntry :: MonadWidget t m
          => m (Event t Op)
taskEntry = do
  el "header" $ do
    newTaskE <- newTaskInput
    -- FIXME a lot of packing and unpacking
    return
      . fmap newTask
      . fmap T.unpack
      . fmapMaybe stripDescription
      . fmap T.pack
      $ newTaskE

newTaskInput :: ( DomBuilder t m, PostBuild t m
                , DomBuilderSpace m ~ GhcjsDomSpace, MonadJSM m
                , TriggerEvent t m
                , MonadHold t m
                , PerformEvent t m
                , MonadJSM (Performable m)
                )
             => m (Event t [Char])
newTaskInput = do
  (e,_) <- elAttr' "input"
           (mconcat [ "type" =: "text"
                    , "class" =: "new-todo"
                    , "name" =: "newTodo"
                    ])
           (return ())
  inputEl <- (unsafeCastTo IE.HTMLInputElement $ _element_raw e)
  keyDownE <- wrapDomEvent inputEl (`on` GEH.keyDown) $
              (do ev <- event
                  key <- KE.getKey ev
                  if key == "Enter"
                    then do val <- IE.getValue inputEl
                            IE.setValue inputEl ("" :: String)
                            return $ Just val
                    else return Nothing)
  return . fmapMaybe id $ keyDownE




-- | Display the user's Tasks, subject to a Filter; return requested
-- modifications to the Task list
taskList :: forall t m.
  (MonadWidget t m)
  => Dynamic t Filter
  -> Dynamic t Tasks
  -> m (Event t Op)
taskList activeFilter tasksD = elAttr "section" ("class" =: "main") $ do
  -- Create "toggle all" button
  let toggleAllState =
        all taskCompleted . Map.elems <$> tasksD
      toggleAllAttrs =
        ffor tasksD $ \t ->
                        "class" =: "toggle-all"
                        <> "name" =: "toggle"
                        <> if Map.null t
                           then "style" =: "visibility:hidden"
                           else mempty
  toggleAll <-
    checkboxView toggleAllAttrs toggleAllState
  elAttr "label" ("for" =: "toggle-all")
    $ text "Mark all as complete"
  -- Filter the item list
  let visibleTasksD :: Dynamic t Tasks =
        zipDynWith (Map.filter . satisfiesFilter) activeFilter tasksD
  -- Hide the item list itself if there are no items
  let itemListAttrs =
        ffor visibleTasksD
        $ \t -> mconcat
                [ "class" =: "todo-list"
                , if Map.null t
                  then "style" =: "visibility:hidden"
                  else mempty
                ]
  -- Display the items
  taskOpsE' :: Event t (Map TaskId TaskOp) <-
    elDynAttr "ul" itemListAttrs
    . listViewWithKey visibleTasksD
    $ (const todoItem)
  let taskOpsE :: Event t Op =
        (map (\(tid, taskOp) -> (Just tid, taskOp))
         . Map.toList)
        <$> taskOpsE'
  -- Aggregate the changes produced by the elements
  let toggleAllOpsE =
        fmap (\(tasks,onOrOff) -> toggleCompleted (not onOrOff) tasks)
        . attach (current tasksD)
        $ tag (current toggleAllState) toggleAll
  return (taskOpsE <> toggleAllOpsE)



-- TODO: Add back cancel editing when an appropriate mechanism
-- exists? (E.g. undo.)
-- | Display an individual todo item
todoItem :: MonadWidget t m
         => Dynamic t Task
         -> m (Event t TaskOp)
todoItem todo = do
  descriptionTxt <- holdUniqDyn
                    . fmap (T.pack . taskDescription)
                    $ todo
  rec -- Construct the attributes for our element
      let attrs =
            zipDynWith (\t e ->
                          "class" =:
                          T.intercalate " " ((if taskCompleted t
                                               then ["completed"]
                                               else [])
                                              <>
                                              (if e
                                                then ["editing"]
                                                else [])))
            todo
            editing'
      (editing', changeTodo) <- elDynAttr "li" attrs $ do
        (setCompletedE, destroyE, startEditing) <-
          elAttr "div" ("class" =: "view") $
          do
            -- Display the todo item's completed status, and allow it to be set
            completed <- holdUniqDyn $ fmap taskCompleted todo
            completedCheckbox <- checkboxView (constDyn $ "class" =: "toggle") completed
            let setCompletedE' =
                  fmap (setCompleted . not)
                  . tag (current completed)
                  $ completedCheckbox
            -- Display the todo item's name for viewing purposes
            (descriptionLabel, _) <- el' "label" $ dynText descriptionTxt
            -- Display the button for deleting the todo item
            (destroyButton, _) <- elAttr' "button" ("class" =: "destroy") $ return ()
            return ( setCompletedE'
                   , destroy <$ domEvent Click destroyButton
                   , domEvent Dblclick descriptionLabel
                   )
        -- Set the current value of the editBox whenever we start
        -- editing (it's not visible in non-editing mode)
        let setEditValue =
              tag (current descriptionTxt)
              . ffilter id
              $ updated editing'
        (editBoxOpE, stopEditingE) <-
          editTaskInput setEditValue
        -- Determine the current editing state; initially false.
        editing <- holdDyn False $ leftmost [ True <$ startEditing
                                            , False <$ stopEditingE
                                            ]
        return ( editing
                 -- Put together all the ways the todo item can change itself.
               , setCompletedE
                 <> destroyE
                 <> (changeDescription <$> editBoxOpE)
               )
  -- Return an event that fires whenever we change ourselves
  return changeTodo

editTaskInput :: ( DomBuilder t m, PostBuild t m
              , DomBuilderSpace m ~ GhcjsDomSpace, MonadJSM m
              , TriggerEvent t m
              , MonadHold t m
              , PerformEvent t m
              , MonadJSM (Performable m)
              , MonadFix m
              )
  => Event t Text
  -> m (Event t (Int, C.SeqIdxOp Char), Event t ())
editTaskInput changeE = do
  -- TODO changeE should remember the cursor position etc.
  (e,_) <- elAttr' "input"
           (mconcat [ "type" =: "text"
                    , "name" =: "title"
                    , "class" =: "edit"
                    ])
           (return ())
  inputEl <- (unsafeCastTo IE.HTMLInputElement $ _element_raw e)
  performEvent_ (IE.setValue inputEl <$> changeE)
  keyDownE <- wrapDomEvent inputEl (`on` GEH.keyDown) $
               do ev <- event
                  caret <- IE.getSelectionStart inputEl
                  key <- KE.getKey ev
                  return $
                   (if length key == 1
                    then Just (caret - 1, C.SeqIns (key List.!! 0))
                    else if (key == "Backspace") && (caret /= 0)
                         then Just (caret - 1, C.SeqDel)
                         else Nothing
                   , if key == "Enter"
                     then Just ()
                     else Nothing
                   )
  blurE <- wrapDomEvent inputEl (`on` GEH.blur) $ return ()
  return $ (fmapMaybe fst keyDownE, fmapMaybe snd keyDownE <> blurE)


-- | Display the control footer; return an event that fires when the
-- user chooses to clear all completed events.
controls :: (DomBuilder t m, PostBuild t m, MonadHold t m, MonadFix m)
  => Dynamic t Tasks
  -> m (Dynamic t Filter, Event t Op)
controls tasks = do
  -- Determine the attributes for the footer; it is invisible when there are no todo items
  let controlsAttrs =
        ffor tasks $ \t ->
                       "class" =: "footer"
                       <> if Map.null t
                          then "style" =: "visibility:hidden"
                          else mempty
  elDynAttr "footer" controlsAttrs $ do
    -- Compute the number of completed and uncompleted tasks
    let (tasksCompleted, tasksLeft) = splitDynPure $ ffor tasks $ \m ->
          let completed = Map.size $ Map.filter taskCompleted m
          in (completed, Map.size m - completed)
    elAttr "span" ("class" =: "todo-count") $ do
      el "strong" $ dynText $ fmap (T.pack . show) tasksLeft
      dynText $ fmap (\n -> (if n == 1 then " item" else " items") <> " left") tasksLeft
    activeFilter <- elAttr "ul" ("class" =: "filters") $ do
      rec activeFilter <- holdDyn All setFilter
          let filterButton f = el "li" $ do
                let buttonAttrs = ffor activeFilter $ \af -> "class" =: if f == af then "selected" else ""
                (e, _) <- elDynAttr' "a" buttonAttrs $ text $ T.pack $ show f
                return $ fmap (const f) (domEvent Click e)
          allButton <- filterButton All
          text " "
          activeButton <- filterButton Active
          text " "
          completedButton <- filterButton Completed
          let setFilter = leftmost [allButton, activeButton, completedButton]
      return activeFilter
    let clearCompletedAttrs = ffor tasksCompleted $ \n -> mconcat
          [ "class" =: "clear-completed"
          , if n > 0 then mempty else "hidden" =: ""
          ]
    (clearCompletedAttrsButton, _) <- elDynAttr' "button" clearCompletedAttrs $ dynText $ ffor tasksCompleted $ \n -> "Clear completed (" <> T.pack (show n) <> ")"
    return ( activeFilter
           , tag
             (current (clearCompleted <$> tasks))
             (domEvent Click clearCompletedAttrsButton)
           )




-- | Display static information about the application
infoFooter :: DomBuilder t m => m ()
infoFooter = do
  elAttr "footer" ("class" =: "info") $ do
    el "p" $ text "Click to edit a todo"
    el "p" $ do
      text "Written by "
      elAttr "a" ("href" =: "https://github.com/ryantrinkle") $ text "Ryan Trinkle"
    el "p" $ do
      text "Part of "
      elAttr "a" ("href" =: "http://todomvc.com") $ text "TodoMVC"

css :: Text
css = " \
    \html,\
    \body {\
    \    margin: 0;\
    \    padding: 0;\
    \}\
    \\
     \button {\
    \    margin: 0;\
    \    padding: 0;\
    \    border: 0;\
    \    background: none;\
    \    font-size: 100%;\
    \    vertical-align: baseline;\
    \    font-family: inherit;\
    \    font-weight: inherit;\
    \    color: inherit;\
    \    -webkit-appearance: none;\
    \    appearance: none;\
    \    -webkit-font-smoothing: antialiased;\
    \    -moz-font-smoothing: antialiased;\
    \    font-smoothing: antialiased;\
    \}\
    \\
     \body {\
    \    font: 14px 'Helvetica Neue', Helvetica, Arial, sans-serif;\
    \    line-height: 1.4em;\
    \    background: #f5f5f5;\
    \    color: #4d4d4d;\
    \    min-width: 230px;\
    \    max-width: 550px;\
    \    margin: 0 auto;\
    \    -webkit-font-smoothing: antialiased;\
    \    -moz-font-smoothing: antialiased;\
    \    font-smoothing: antialiased;\
    \    font-weight: 300;\
    \}\
    \\
     \button,\
    \input[type=\"checkbox\"] {\
    \    outline: none;\
    \}\
    \\
     \.hidden {\
    \    display: none;\
    \}\
    \\
     \.todoapp {\
    \    background: #fff;\
    \    margin: 130px 0 40px 0;\
    \    position: relative;\
    \    box-shadow: 0 2px 4px 0 rgba(0, 0, 0, 0.2),\
    \                0 25px 50px 0 rgba(0, 0, 0, 0.1);\
    \}\
    \\
     \.todoapp input::-webkit-input-placeholder {\
    \    font-style: italic;\
    \    font-weight: 300;\
    \    color: #e6e6e6;\
    \}\
    \\
     \.todoapp input::-moz-placeholder {\
    \    font-style: italic;\
    \    font-weight: 300;\
    \    color: #e6e6e6;\
    \}\
    \\
     \.todoapp input::input-placeholder {\
    \    font-style: italic;\
    \    font-weight: 300;\
    \    color: #e6e6e6;\
    \}\
    \\
     \.todoapp h1 {\
    \    top: -155px;\
    \    position: absolute;\
    \    width: 100%;\
    \    font-size: 100px;\
    \    font-weight: 100;\
    \    text-align: center;\
    \    color: rgba(175, 47, 47, 0.15);\
    \    -webkit-text-rendering: optimizeLegibility;\
    \    -moz-text-rendering: optimizeLegibility;\
    \    text-rendering: optimizeLegibility;\
    \}\
    \\
     \.new-todo,\
    \.edit {\
    \    position: relative;\
    \    margin: 0;\
    \    width: 100%;\
    \    font-size: 24px;\
    \    font-family: inherit;\
    \    font-weight: inherit;\
    \    line-height: 1.4em;\
    \    border: 0;\
    \    outline: none;\
    \    color: inherit;\
    \    padding: 6px;\
    \    border: 1px solid #999;\
    \    box-shadow: inset 0 -1px 5px 0 rgba(0, 0, 0, 0.2);\
    \    box-sizing: border-box;\
    \    -webkit-font-smoothing: antialiased;\
    \    -moz-font-smoothing: antialiased;\
    \    font-smoothing: antialiased;\
    \}\
    \\
     \.new-todo {\
    \    padding: 16px 16px 16px 60px;\
    \    border: none;\
    \    background: rgba(0, 0, 0, 0.003);\
    \    box-shadow: inset 0 -2px 1px rgba(0,0,0,0.03);\
    \}\
    \\
     \.main {\
    \    position: relative;\
    \    z-index: 2;\
    \    border-top: 1px solid #e6e6e6;\
    \}\
    \\
     \label[for='toggle-all'] {\
    \    display: none;\
    \}\
    \\
     \.toggle-all {\
    \    position: absolute;\
    \    top: -55px;\
    \    left: -12px;\
    \    width: 60px;\
    \    height: 34px;\
    \    text-align: center;\
    \    border: none; /* Mobile Safari */\
    \}\
    \\
     \.toggle-all:before {\
    \    content: '❯';\
    \    font-size: 22px;\
    \    color: #e6e6e6;\
    \    padding: 10px 27px 10px 27px;\
    \}\
    \\
     \.toggle-all:checked:before {\
    \    color: #737373;\
    \}\
    \\
     \.todo-list {\
    \    margin: 0;\
    \    padding: 0;\
    \    list-style: none;\
    \}\
    \\
     \.todo-list li {\
    \    position: relative;\
    \    font-size: 24px;\
    \    border-bottom: 1px solid #ededed;\
    \}\
    \\
     \.todo-list li:last-child {\
    \    border-bottom: none;\
    \}\
    \\
     \.todo-list li.editing {\
    \    border-bottom: none;\
    \    padding: 0;\
    \}\
    \\
     \.todo-list li.editing .edit {\
    \    display: block;\
    \    width: 506px;\
    \    padding: 13px 17px 12px 17px;\
    \    margin: 0 0 0 43px;\
    \}\
    \\
     \.todo-list li.editing .view {\
    \    display: none;\
    \}\
    \\
     \.todo-list li .toggle {\
    \    text-align: center;\
    \    width: 40px;\
    \    /* auto, since non-WebKit browsers doesn't support input styling */\
    \    height: auto;\
    \    position: absolute;\
    \    top: 0;\
    \    bottom: 0;\
    \    margin: auto 0;\
    \    border: none; /* Mobile Safari */\
    \    -webkit-appearance: none;\
    \    appearance: none;\
    \}\
    \\
     \.todo-list li .toggle:after {\
    \    content: url('data:image/svg+xml;utf8,<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"40\" height=\"40\" viewBox=\"-10 -18 100 135\"><circle cx=\"50\" cy=\"50\" r=\"50\" fill=\"none\" stroke=\"#ededed\" stroke-width=\"3\"/></svg>');\
    \}\
    \\
     \.todo-list li .toggle:checked:after {\
    \    content: url('data:image/svg+xml;utf8,<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"40\" height=\"40\" viewBox=\"-10 -18 100 135\"><circle cx=\"50\" cy=\"50\" r=\"50\" fill=\"none\" stroke=\"#bddad5\" stroke-width=\"3\"/><path fill=\"#5dc2af\" d=\"M72 25L42 71 27 56l-4 4 20 20 34-52z\"/></svg>');\
    \}\
    \\
     \.todo-list li label {\
    \    white-space: pre;\
    \    word-break: break-word;\
    \    padding: 15px 60px 15px 15px;\
    \    margin-left: 45px;\
    \    display: block;\
    \    line-height: 1.2;\
    \    transition: color 0.4s;\
    \}\
    \\
     \.todo-list li.completed label {\
    \    color: #d9d9d9;\
    \    text-decoration: line-through;\
    \}\
    \\
     \.todo-list li .destroy {\
    \    display: none;\
    \    position: absolute;\
    \    top: 0;\
    \    right: 10px;\
    \    bottom: 0;\
    \    width: 40px;\
    \    height: 40px;\
    \    margin: auto 0;\
    \    font-size: 30px;\
    \    color: #cc9a9a;\
    \    margin-bottom: 11px;\
    \    transition: color 0.2s ease-out;\
    \}\
    \\
     \.todo-list li .destroy:hover {\
    \    color: #af5b5e;\
    \}\
    \\
     \.todo-list li .destroy:after {\
    \    content: '×';\
    \}\
    \\
     \.todo-list li:hover .destroy {\
    \    display: block;\
    \}\
    \\
     \.todo-list li .edit {\
    \    display: none;\
    \}\
    \\
     \.todo-list li.editing:last-child {\
    \    margin-bottom: -1px;\
    \}\
    \\
     \.footer {\
    \    color: #777;\
    \    padding: 10px 15px;\
    \    height: 20px;\
    \    text-align: center;\
    \    border-top: 1px solid #e6e6e6;\
    \}\
    \\
     \.footer:before {\
    \    content: '';\
    \    position: absolute;\
    \    right: 0;\
    \    bottom: 0;\
    \    left: 0;\
    \    height: 50px;\
    \    overflow: hidden;\
    \    box-shadow: 0 1px 1px rgba(0, 0, 0, 0.2),\
    \                0 8px 0 -3px #f6f6f6,\
    \                0 9px 1px -3px rgba(0, 0, 0, 0.2),\
    \                0 16px 0 -6px #f6f6f6,\
    \                0 17px 2px -6px rgba(0, 0, 0, 0.2);\
    \}\
    \\
     \.todo-count {\
    \    float: left;\
    \    text-align: left;\
    \}\
    \\
     \.todo-count strong {\
    \    font-weight: 300;\
    \}\
    \\
     \.filters {\
    \    margin: 0;\
    \    padding: 0;\
    \    list-style: none;\
    \    position: absolute;\
    \    right: 0;\
    \    left: 0;\
    \}\
    \\
     \.filters li {\
    \    display: inline;\
    \}\
    \\
     \.filters li a {\
    \    color: inherit;\
    \    margin: 3px;\
    \    padding: 3px 7px;\
    \    text-decoration: none;\
    \    border: 1px solid transparent;\
    \    border-radius: 3px;\
    \}\
    \\
     \.filters li a.selected,\
    \.filters li a:hover {\
    \    border-color: rgba(175, 47, 47, 0.1);\
    \}\
    \\
     \.filters li a.selected {\
    \    border-color: rgba(175, 47, 47, 0.2);\
    \}\
    \\
     \.clear-completed,\
    \html .clear-completed:active {\
    \    float: right;\
    \    position: relative;\
    \    line-height: 20px;\
    \    text-decoration: none;\
    \    cursor: pointer;\
    \    position: relative;\
    \}\
    \\
     \.clear-completed:hover {\
    \    text-decoration: underline;\
    \}\
    \\
     \.info {\
    \    margin: 65px auto 0;\
    \    color: #bfbfbf;\
    \    font-size: 10px;\
    \    text-shadow: 0 1px 0 rgba(255, 255, 255, 0.5);\
    \    text-align: center;\
    \}\
    \\
     \.info p {\
    \    line-height: 1;\
    \}\
    \\
     \.info a {\
    \    color: inherit;\
    \    text-decoration: none;\
    \    font-weight: 400;\
    \}\
    \\
     \.info a:hover {\
    \    text-decoration: underline;\
    \}\
    \\
     \/*\
    \    Hack to remove background from Mobile Safari.\
    \    Can't use it globally since it destroys checkboxes in Firefox\
    \*/\
    \@media screen and (-webkit-min-device-pixel-ratio:0) {\
    \    .toggle-all,\
    \    .todo-list li .toggle {\
    \     background: none;\
    \    }\
    \\
     \    .todo-list li .toggle {\
    \       height: 40px;\
    \    }\
    \\
     \    .toggle-all {\
    \       -webkit-transform: rotate(90deg);\
    \       transform: rotate(90deg);\
    \       -webkit-appearance: none;\
    \       appearance: none;\
    \    }\
    \}\
    \\
     \@media (max-width: 430px) {\
    \    .footer {\
    \       height: 50px;\
    \    }\
    \\
     \    .filters {\
    \       bottom: 10px;\
    \    }\
    \}"
