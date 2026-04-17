# _MVM (Model Validator Mixer)_


## Table of Contents

- [Introduction](#introduction)
  - [MVM – Overview](#mvm--overview)
- [Instructions for installation for testing](#instructions-for-installation-for-testing)
- [Strategy](#strategy)
  - [Consistency Check](#consistency-check)
  - [Diagnosis](#diagnosis)
  - [Validation](#validation)
  - [Guided Interactive Repair](#guided-interactive-repair)
- [MVM TOOL](#mvm-tool)
  - [Brute force](#brute-force)
    - [Errors](#errors)
    - [Best approximate solutions](#best-approximate-solutions)
    - [Statistics](#statistics)
  - [Greedy](#greedy)
  - [Creación diagrama desde diálogo MUS/MSS](#creación-diagrama-desde-diálogo-musmss)
- [MVM Wizard](#mvm-wizard)
  - [1: Classes](#1-classes)
  - [2: Objects](#2-objects)
  - [3: Attributes](#3-attributes)
  - [4: Object](#4-object)
  - [5: New object](#5-new-object)
  - [6: Save object](#6-save-object)
  - [7: Cancel object](#7-cancel-object)
  - [8: Delete object](#8-delete-object)
  - [9: +](#9-)
  - [10: Fill](#10-fill)
  - [11: Auto Layout](#11-auto-layout)
  - [12: Refresh](#12-refresh)
  - [13: Reset](#13-reset)
  - [14: Associations](#14-associations)
  - [15: From Class](#15-from-class)
  - [16: To Class](#16-to-class)
  - [17: From Object](#17-from-object)
  - [18: To Object](#18-to-object)
  - [19: From multiplicity](#19-from-multiplicity)
  - [20: To multiplicity](#20-to-multiplicity)
  - [21: From Role](#21-from-role)
  - [22: To Role](#22-to-role)
  - [23: Insert link](#23-insert-link)
  - [24: Delete link](#24-delete-link)
  - [25: Actions](#25-actions)
  - [26: Suggest fixes](#26-suggest-fixes)
  - [27: State invariants](#27-state-invariants)
  - [28: OBJs](#28-objs)
  - [29: Multiplicities](#29-multiplicities)
  - [30: MSS/MUS](#30-mssmus)
- [MVM Check Objects Satisfiability](#mvm-check-objects-satisfiability)
  - [1: Filter Objects](#1-filter-objects)
  - [2: Incorrect/Correct](#2-incorrectcorrect)
  - [3: Filter Invariants](#3-filter-invariants)
  - [4: Objects](#4-objects)
  - [5: Invariants](#5-invariants)
  - [6: Attributes](#6-attributes)
  - [7: Current invariant body](#7-current-invariant-body)
  - [8: Body alternatives](#8-body-alternatives)
  - [9: Filter Alternatives](#9-filter-alternatives)
  - [10: New Invariant body - Incorrect/Correct](#10-new-invariant-body---incorrectcorrect)
  - [11: Test](#11-test)
  - [13: Body expression](#13-body-expression)
  - [14: Show Source](#14-show-source)
  - [15: File Name](#15-file-name)
  - [16: Save file](#16-save-file)
  - [17: Exit](#17-exit)
- [Wizard Association](#wizard-association)
  - [1: Associations](#1-associations)
  - [2: Links](#2-links)
  - [3: Cause](#3-cause)
  - [4: Full Message](#4-full-message)
  - [5: Proposals](#5-proposals)
  - [6: Apply](#6-apply)
  - [7: Exit](#7-exit)
  - [Example multiplicities](#example-multiplicities)
- [Actions](#actions)
  - [1: File Name](#1-file-name)
  - [2: Creation Date](#2-creation-date)
  - [3: Mod. Date](#3-mod-date)
  - [4: Model](#4-model)
  - [5: Source USE File](#5-source-use-file)
  - [6: Description](#6-description)
  - [7: Actions](#7-actions)
  - [8: Objects](#8-objects)
  - [9: Attributes](#9-attributes)
  - [10: Open actions](#10-open-actions)
  - [11: Find Actions](#11-find-actions)
  - [12: Save actions](#12-save-actions)
  - [13: Load actions](#13-load-actions)
  - [14: Links](#14-links)
  - [15: Exit](#15-exit)
- [ACKNOWLEDGMENT](#acknowledgment)
- [CITATION](#citation)
- [REFERENCES](#references)


# Introduction

This project is a extension of the **USE** Model Validator plug-in from Martin Gogolla, Fabian Büttner, and Mark Richters 
for the UML-Based Specification Environment (https://sourceforge.net/projects/useocl/). The code is developed in Java.

[(Up)](#Table-of-Contents)

## MVM – Overview
MVM is the tool that supports our detection, validation, and repair strategy proposed in the following works:
- Tool for Debugging Unsatisfiable Integrity Constraints in UML/OCL Class Diagrams (EMMSAD 2020)
- Interactive Repair of Inconsistencies (ER 2025)
- Interactive Repair in Conceptual Models Using LLM

As a strategy, MVM could have been implemented in various programming languages. However, since we decided to use the USE tool as a starting point, MVM is developed in Java and implemented as an extension of USE.

This approach allows MVM to:
- Reuse many of the standard functionalities provided by USE
- Extend the environment with additional capabilities
- Leverage the robust and well‑established ecosystem of the USE tool


Author: ***Juan Antonio Gómez Gutiérrez(2025)***

[(Up)](#Table-of-Contents)

----

# Instructions for installation for testing

To download and use MVM, simply follow these steps:
1. Download the zip file from the following link:

https://drive.google.com/file/d/1w6wcO8XAaGcZxgyI_BUNQxnjqLepJOwL/view?usp=sharing

2. Have Java 11 (or higher) installed. If you don't have it, download it from the following link:
https://adoptium.net/es/temurin/releases?version=11

3. Define the OPENAI_API_KEY environment variable with the key that allows the use of OpenAI. For example, open a CMD session and enter the following (each user has their own key):
```
**setx OPENAI_API_KEY sk-proj-------xxxxxxxxx---------K-NOFAoA**
```
Once you've downloaded the zip file to any folder, extract it and then simply run **RUN** (or RUN nameFile)  bat from the extracted folder.
If everything goes well, you should see the following:

<img width="650" height="213" alt="image" src="https://github.com/user-attachments/assets/c2a171a4-e6b3-488f-ba37-da9d90cd2242" />

<img width="650" height="460" alt="image" src="https://github.com/user-attachments/assets/a4d657ec-5b69-40bd-8355-440cf757e30e" />

[(Up)](#Table-of-Contents)

# Strategy
Our strategy includes the following sections:

## Consistency Check  
Determine if a UML/OCL diagram is consistent.

## Diagnosis  
Identify the unsatisfactory core, the minimum subsets of constraints involved in the inconsistency, as well as example instances that satisfy the maximum number of constraints in the model.

## Validation  
Create, visualize, and modify instances using a graphical user interface, and evaluate the validity of model constraints in the context of that instance.

## Guided Interactive Repair  
Propose possible solutions to identified inconsistencies—both graphical constraints in the class diagram (such as multiplicities) and textual constraints (such as OCL invariants).
Evaluate the suitability of such candidate solutions and allow reversing previous decisions if they are deemed inadequate.

In addition to determining whether a model is satisfactory or not, the intention is to indicate which elements cause unsatisfactoriness and propose alternatives for their repair, including the possibility of creating instances that demonstrate the viability of the model.

[(Up)](#Table-of-Contents)

# MVM TOOL
Search for MUS/MSS
The first functionality that MVM provided was the search for **MUS (Minimum Unsatisfiable Core)** and **MSS (Maximum Satisfiable Subset)**.
To achieve this, MVM constructs all possible combinations between the invariants of the model and, relying on the Solver used by USE (kodkodSolver), generates lists containing groups of satisfiable and unsatisfiable invariants.

The calculation of **MUS/MSS** can be performed in two ways:
- **Brute force method**:  Searches all combinations before presenting any results.
- **Greedy method**: Finds an initial group of invariants that are not related to each other and provides a result immediately, allowing the user to begin working while the system continues processing the remaining combinations in the background.

Both methods are available in the menu or toolbar.
![](https://github.com/juanto2021/MVM/blob/main/imgREADME/01_01_MUS_menu_bar.png)

## Brute force
When this option is executed, the search for all combinations between invariants is launched in order to internally build the lists of groups of satisfactory and unsatisfactory combinations.
Depending on the number of existing invariants, this search may take a considerable amount of time.

If the user wishes, they can stop this search by clicking on the **Stop calculating combinations** icon:

![Stop calculating combinations](imgREADME/01_02_stopCalculateCmb.png)

If you click on this option, a message will appear requesting confirmation:

<img src="imgREADME/01_03_ConfirmStop.png" width="400">

When the search for combinations is complete, a dialog box appears containing the following tabs:
- **Errors**: Displays groups of combinations that fail when active. Any set of joins that includes any of the groups shown in this tab will produce an unsatisfactory instance.
- **Best approximate solutions**: Shows the groups of combinations that can be active simultaneously and that would produce a satisfactory instance.
- **Statistics**: Provides statistical information such as:
  - total time required to compute all combinations
  - number of calls to the Solver
  - number of satisfactory and unsatisfactory combinations

In the title of the dialog box, you can see the selected method (Brute) and the name of the model being analyzed (Animals).

[(Up)](#Table-of-Contents)

### Errors
<!-- <img src="imgREADME/01_04_Errors.png" width="400"> -->
<img src="imgREADME/01_04_Errors.png">

On this screen we can see different blocks that interact with each other so that, when we click on a row in the Faulty combinations panel, the rest of the blocks are synchronized and show the detail associated with the selected group.

**_Panels_**

- **Faulty combinations**: In this example, we can see that 3 groups of **MUS**  (**6**, **4-8** and **5-8**) have been detected. If we click on the first group (it contains the invariant **'6'**), we will see that the panel on the right shows the selected combination **'6'** as the title and inside it a line for each invariant of that combination.
-	**'6'**: panel showing all the invariants that make up the selected MUS group (**'6'**). When you select a line from this block, the **instances without inv** and **OCL for inv Example panes** synchronize by displaying information associated with the invariant of the selected line.
-	**Example of instances without inv: '6'**: proposes satisfactory combinations that do not contain the  selected **MUS** group  and that can generate a satisfactory instance by simply double-clicking on any of its lines (e.g. **'1-2-3-4-5-7'**).
-	**OCL for inv: '6'**: Displays the definition of the selected invariant to have a view of the possible problem to be solved. In this example it is clear that age cannot be simultaneously **<=0 and >99**.

The **Close** button closes the dialog box and returns to the previous screen.

[(Up)](#Table-of-Contents)

### Best approximate solutions
<img src="imgREADME/01_05_BestSolutions.png">

In this tab, we can see the groups of joins that can generate satisfactory instances as long as the rest of the invariants that do not appear are disabled. Note that the groups are ordered from the highest number of satisfactory invariants to the least. 

**_Panels_**

The blocks that make up this tab are:
- **Invariants**: Groups of invariants that generate a satisfactory instance. Similar to the one described in **Errors**, if we double-click on any line of the Invariants block, an instance is created and an object diagram opens showing it.
-	**'1-2-3-4-5-7'**: shows the invariants that make up the group with their name.
-	**OCL for inv: 1-Person::valildGreaterThanAge**: Displays the bodyexpression of the invariant selected in the previous block.

[(Up)](#Table-of-Contents)

### Statistics
<img src="imgREADME/01_06_Statistics.png">

**_Panels_**

It displays the following information:
-	**Execution time**: The time it takes for the process to complete.
-	**Number of calls to the solver**: number of calls that are actually made to the solver.
-	**Number of satisfied calls**: solver calls that are satisfactory.
-	**Number of unsatisfied calls**: Calls to the solver that are unsatisfactory.
-	**Total number of combinations**: Total number of combinations. 
-	**Total number of satisfiable combinations**: number of total satisfactory combinations.
-	**Total number of combinations unsatisfiable**: number of total unsatisfactory combinations.

[(Up)](#Table-of-Contents)

## Greedy

Similar to **Brute force**, the **Greedy method** also searches for **MUS** and **MSS**, but it does so in 2 phases:
-	**Look for a first result with satisfactory invariants**.
-	**Look for the rest of the pending combinations**.

In the first phase, **Greedy** determines the dependence of each invariant on the others by analyzing attributes and classes involved in it and fabricates a collection of invariants that do not interfere with each other. In this way, almost instantaneously we obtain a first result with which to produce a satisfactory instance. 

The second phase looks for the rest of the pending combinations until all the possible ones are completed.

Regarding the dialog box shown during the search, it should be noted that when Greedy gives the first result, in the title of the dialog, in addition to the Greedy method,  the word Initial is also shown  indicating that it is the first result. When the Greedy combination search is complete, End is displayed.

<img src="imgREADME/01_07_Greedy.png">

[(Up)](#Table-of-Contents)

## Creación diagrama desde diálogo MUS/MSS

To create an object diagram, simply double-click on one of the combinations shown in the Errors tab  or in Best approximate solutions:

<img src="imgREADME/01_08_DO.png" width="3000">

[(Up)](#Table-of-Contents)

# MVM Wizard 
This screen is the main screen from which the vast majority of the functionalities contained in MVM can be used or accessed.

It is basically divided into 3 blocks:
-	**Elements**: Manages existing objects in the current instance (additions, deletions, modifications, and queries)
-	**Associations**: Manage existing links between objects
-	**Actions**: access the utilities for repairing invariants, multiplicities, log of actions performed and consult OpenAI.

<img src="imgREADME/02_01_Wizard_main.png">

Below, we detail the purpose of each graphic element.

## 1: Classes
Displays the existing classes in the model. When you click on a class, the **Objects** and **Attributes** blocks synchronize to show the existing objects of the selected class and the attributes and their values of the first object of that class.

<img src="imgREADME/02_02_Classes.png">

[(Up)](#Table-of-Contents)

## 2: Objects
Displays the existing objects in the current instance of the class selected in the **Classes** block. Each time an object is selected, the **Attributes table** displays its corresponding attributes and values.

<img src="imgREADME/02_03_Objects.png">

[(Up)](#Table-of-Contents)

## 3: Attributes
It allows you to visualize and modify the attributes and values of an object. In the case of an existing object, you can modify a value by selecting it and then clicking on the value you want to modify.

<img src="imgREADME/02_21_Attr.png">

The values assigned to the attributes of type String must be enclosed in single quotation marks ('**Example String**').

When a value is modified, the **Save Obj** and **Cancel Obj** buttons are enabled  to make the changes permanent or leave the object as it was without changing anything respectively.

If you enter a value that does not correspond to the expected type, an error message appears:

<img src="imgREADME/02_04_err_type.png">

[(Up)](#Table-of-Contents)


## 4: Object

This text box is used to display the **ID** of the object that has the focus and is disabled when the treated object already exists. However, when we click on the **New Obj** button, it is enabled so that we can enter a new **ID**:

<img src="imgREADME/02_05_new_obj.png">

If we enter an **ID** that already exists and click on **Save Obj**, an error message appears:

<img src="imgREADME/02_06_new_obj_ya_existe.png">

If we want to leave the object as it was before changing anything, we will simply press **Cancel Obj**.

[(Up)](#Table-of-Contents)

## 5: New object

Pressing this button enables the Object text box  to enter an **ID** and leaves the values in the attributes so that we can modify only those that are necessary.

<img src="imgREADME/02_07_new_obj02.png">

[(Up)](#Table-of-Contents)

## 6: Save object

[(Up)](#Table-of-Contents)

Applies to the instance the modifications made to the object.

[(Up)](#Table-of-Contents)

## 7: Cancel object

Leaves the object with the values it had before you modified it and clicked **Save Obj**.

[(Up)](#Table-of-Contents)

## 8: Delete object

Allows you to delete the selected object, but first requests confirmation with this message:

<img src="imgREADME/02_08_Confirm_Delete.png">

[(Up)](#Table-of-Contents)

## 9: +

Allows you to create an object by copying the selected object. The **object ID** will be the name of the class followed by a number that it will get from a sequential number within the class. 

<img src="imgREADME/02_21_MasMas.png">

[(Up)](#Table-of-Contents)

## 10: Fill

Create one object of each class. The **object ID** will be the name of the class followed by a number that it will get from a sequential number within the class. 

<img src="imgREADME/02_20_FillObj.png">

Initialize attributes depending on their type:
-	**String**: ‘x’.
-	**Boolean**: true
-	**Integer**: 1
-	**Real**: 1.0.

[(Up)](#Table-of-Contents)

## 11: Auto Layout

**Enables**/**disables** the feature that automatically places objects on the diagram in a manner spaced apart.	

[(Up)](#Table-of-Contents)

## 12: Refresh

Recreate the elements of the diagram.

[(Up)](#Table-of-Contents)

## 13: Reset

Deletes all objects from the instance and flushes the diagram.

[(Up)](#Table-of-Contents)

## 14: Associations

Lists the associations defined in the model.

<img src="imgREADME/02_09_Associations.png">

[(Up)](#Table-of-Contents)

Selecting an association synchronizes the '**From**' and '**To**' information on the right.

## 15: From Class
Displays the **participating class** at the origin endpoint.

<img src="imgREADME/02_10_FromClass.png">

[(Up)](#Table-of-Contents)

## 16: To Class

Displays the **participating class** at the end endpoint.

<img src="imgREADME/02_11_ToClass.png">

[(Up)](#Table-of-Contents)

## 17: From Object

Displays the **participating object** at the source endpoint.

<img src="imgREADME/02_12_FromObject.png">

[(Up)](#Table-of-Contents)

## 18: To Object

Displays the **participating object** at the end endpoint.

<img src="imgREADME/02_13_ToObject.png">

[(Up)](#Table-of-Contents)

## 19: From multiplicity

**Multiplicity** at the **origin** extreme.

<img src="imgREADME/02_14_FromMultiplicity.png">

[(Up)](#Table-of-Contents)

## 20: To multiplicity

**Multiplicity** at the **endpoint**.

<img src="imgREADME/02_15_ToMultiplicity.png">

[(Up)](#Table-of-Contents)

## 21: From Role

**Role** on the **origin** endpoint.

<img src="imgREADME/02_16_FromRole.png">

[(Up)](#Table-of-Contents)

## 22: To Role

**Role** at the **end** endpoint.

<img src="imgREADME/02_17_ToRole.png">

[(Up)](#Table-of-Contents)

## 23: Insert link

It allows you to insert a link between 2 objects. To do this, we have to select the source object and the final object and click on the **Insert Link button**:

<img src="imgREADME/02_18_InsertLink.png">

[(Up)](#Table-of-Contents)

## 24: Delete link

Allows you to delete a link between 2 objects. To select a link, we can select the objects that are at each end or click on it in the diagram.

<img src="imgREADME/02_19_DeleteLink.png">

[(Up)](#Table-of-Contents)

## 25: Actions

This button allows access to **MVM Wizard Actions**, which is the functionality in charge of managing the record of the actions carried out on a given instance.

<img src="imgREADME/03_16_ActionsCall.png">

With this functionality, the user will be able to record a set of actions and retrieve them later to reproduce a given situation on the instance. You can even go back to a specific situation without needing to record any files beforehand.

[(Up)](#Table-of-Contents)

## 26: Suggest fixes

This button allows **OpenAI** to be invoked  to perform a query that allows us to get suggestions to detect errors in the model and correct them.

<img src="imgREADME/03_17_OpenAIcall.png">

[(Up)](#Table-of-Contents)

## 27: State invariants

This section allows you to review the status of invariants. The color of the button indicates whether all the invariants are met or not so that, at a glance, we can check the status of the instance as far as invariants are concerned.

If we click on it, a screen appears where we can see which invariants are satisfied and which are not.

<img src="imgREADME/05_SI_01_CheckInvs.png">

[(Up)](#Table-of-Contents)

## 28: OBJs

This button allows access to the functionality that tells us which invariants are failing according to the existing objects in the instance and which are the alternatives proposed for their solution. The color of the button will depend on whether the invariants are satisfied or not.

<img src="imgREADME/05_SI_24_OBJ_Call.png">

[(Up)](#Table-of-Contents)

## 29: Multiplicities

This button gives access to the screen that determines the multiplicity problems encountered in the current instance and helps to solve them by proposing the **creation**/**deletion** of objects and the creation of links between them.

<img src="imgREADME/03_16_ActionsCall.png">

[(Up)](#Table-of-Contents)

## 30: MSS/MUS

Using this button, if accessible, we can display the dialog box that shows the previously obtained **MUS**/**MSS**. If it is not accessible, it means that they have not yet been calculated. It is equivalent to clicking on the icon that we have in the toolbar:

<img src="imgREADME/07_01_MUS_MSS01.png">

When you click on this option, you will see the dialog associated with the **MUS**/**MSS**:

<img src="imgREADME/03_18_MUS_MSS_call.png">

[(Up)](#Table-of-Contents)

# MVM Check Objects Satisfiability

This button also changes color depending on whether the invariants are satisfied or not. Clicking on it gives access to the following MVM  Check Objects 

**Satisfiability screen**:

<img src="imgREADME/05_SI_02_OBJ_Main.png">

This screen shows the existing objects in the instance and for each object, the invariants in which they participate and also the associated attributes and values. Each time an object is selected, the other blocks are synchronized to display the information associated with it. Therefore, if an object appears as false in the **Satisfied** column, there is surely at least one invariant that is not satisfied for it.

Below, we comment on the graphic elements that make it up.

[(Up)](#Table-of-Contents)

## 1: Filter Objects

This group of options allows you to display objects according to the selected option:

| Vista    | Imagen |
|----------|--------|
| All      | <img src="imgREADME/05_SI_03_OBJ_FilObj1.png"> |
| Correct  | <img src="imgREADME/05_SI_04_OBJ_FilObj2.png"> |
| Incorrect| <img src="imgREADME/05_SI_05_OBJ_FilObj3.png"> |

[(Up)](#Table-of-Contents)

## 2: Incorrect/Correct

This label shows the general state of the instance so that at a glance it can be easily cataloged:

<img src="imgREADME/05_SI_06_OBJ_CorrectIncorrect.png">

[(Up)](#Table-of-Contents)

## 3: Filter Invariants

When we select an object, the invariant block shows all the invariants in which it participates. In this case, it may be interesting to show them all, or only the correct or incorrect ones.

| Vista    | Imagen |
|----------|--------|
| All      | <img src="imgREADME/05_SI_07_OBJ_Inv1.png"> |
| Correct  | <img src="imgREADME/05_SI_08_OBJ_Inv2.png"> |
| Incorrect| <img src="imgREADME/05_SI_09_OBJ_Inv3.png"> |

[(Up)](#Table-of-Contents)

## 4: Objects

Displays the existing objects on the instance. When clicked, the rest of the blocks are synchronized to show the information associated with it.

<img src="imgREADME/05_SI_10_OBJ_Objs.png">

[(Up)](#Table-of-Contents)

## 5: Invariants

Displays the invariants associated with the selected object.

<img src="imgREADME/05_SI_11_OBJ_Invs.png">

[(Up)](#Table-of-Contents)

## 6: Attributes

Displays the attributes associated with the selected object.

<img src="imgREADME/05_SI_12_OBJ_Attrs.png">

[(Up)](#Table-of-Contents)

## 7: Current invariant body

Displays the bodyexpression currently held by the selected invariant.

<img src="imgREADME/05_SI_13_OBJ_CurrentBody.png">

[(Up)](#Table-of-Contents)

## 8: Body alternatives

Displays the alternatives that have been calculated for the selected invariant.

<img src="imgREADME/05_SI_14_OBJ_BodyAlternatives.png">

For each of the proposed alternatives, the system calculates its satisfactibility.

[(Up)](#Table-of-Contents)

## 9: Filter Alternatives

It allows you to visualize all the alternatives, only the correct ones or only the wrong ones.

| Vista    | Imagen |
|----------|--------|
| All      | <img src="imgREADME/05_SI_15_OBJ_FilAlt1.png"> |
| Correct  | <img src="imgREADME/05_SI_16_OBJ_FilAlt2.png"> |
| Incorrect| <img src="imgREADME/05_SI_17_OBJ_FilAlt3.png"> |

[(Up)](#Table-of-Contents)

## 10: New Invariant body - Incorrect/Correct

This label shows the result of the test of the alternative whose definition is found in the text box just below (13: Body expression). It can have any of the following values:

<img src="imgREADME/05_SI_18_OBJ_StateTest.png">

The ‘questions’ are displayed when the text box containing the definition of the bodyexpression receives focus and disappear when it loses it. 

[(Up)](#Table-of-Contents)

## 11: Test

This button allows you to run the test to check that the **bodyexpression** of the alternative in the text box is correct.

[(Up)](#Table-of-Contents)

## 12: Model viable

This text allows you to check whether the model definition has a good syntax or not after the replacement of the new **bodyexpression** over the old one.
Examples:

| Correct | Incorrect |
|--------|-----------|
| <img src="imgREADME/05_SI_19_01_OBJ_Viable1.png"> | <img src="imgREADME/05_SI_19_02_OBJ_Viable2.png"> |

[(Up)](#Table-of-Contents)

## 13: Body expression

This text box contains the bodyexpression that will replace the current one in the treated invariant in the new model. When we click on an alternative, the associated expression is placed in this text box. If the user wants, they can modify it manually and that's when questions appear on the label above this text box.

<img src="imgREADME/05_SI_20_OBJ_NewBody.png">

[(Up)](#Table-of-Contents)

## 14: Show Source

It shows a screen with 2 parts: 
-	The **current one**
-	the **new one** as it would be after replacing the invariant with the alternative

This screen looks like this:

<img src="imgREADME/05_SI_21_OBJ_ShowSource.png">

In it you can see the old definition of the invariant **Availability**, and the new one. Note that the old definition is converted to a comment (**--**) for the record, and the new one is added below.

It is possible to synchronize both panels (**Current** and **New**) by activating the **Sync scroll** check.

[(Up)](#Table-of-Contents)

## 15: File Name

Indicate the name of the file to be proposed. The first proposal will be to add the suffix **_vX** with **X** being the version number that already exists. If no version exists, the suffix will be **_v1**. If a previous version exists, such as **_v4**, the proposed version will be **_v5**.

The default target directory will be **wrkReplaceBodyInv** which will be inside the working directory where the application is running.

<img src="imgREADME/05_SI_23_OBJ_DirWorkFile.png">

If this directory does not exist, it will be created automatically.
 
[(Up)](#Table-of-Contents)

## 16: Save file

This button allows you to save a file with the new model in which the previously selected invariant has been modified, replacing its definition with the new definition entered in the New invariant body text box.

Clicking on it will open the File to Save dialog proposing the default directory and name, but the user can modify what is necessary according to their criteria:

<img src="imgREADME/05_SI_22_OBJ_SaveFile.png">

[(Up)](#Table-of-Contents)

## 17: Exit

Allows you to close the screen in progress and return to the previous one.

[(Up)](#Table-of-Contents)


# Wizard Association

This button gives access to the screen that helps solve problems of multiplicity by proposing the creation/deletion of objects and the creation of links between them.

The main screen of this utility is composed of the following graphic elements:

<img src="imgREADME/06_01_Multiplicities_Main.png">

[(Up)](#Table-of-Contents)

## 1: Associations

Displays the list of associations that have a problem. When you click on an association, the rest of the blocks on the screen are synchronized to show the information of the links associated with it.

[(Up)](#Table-of-Contents)

## 2:Links

Displays objects that are potentially related to the selected association. When you click on a link, you will see that the rest of the blocks (except **Associations**) synchronize to show information related to the selected link.

[(Up)](#Table-of-Contents)

## 3: Cause

It shows the **cause** why the link is failing.

[(Up)](#Table-of-Contents)

## 4: Full Message

Displays the **full** error message associated with the selected link. 

[(Up)](#Table-of-Contents)

## 5: Proposals

It shows the proposals envisaged to try to solve the problem of multiplicity.

The proposals that are made are based on the following actions:
-	**Create elements** that help respect the cardinality of links
-	**Assign elements** to create links
-	**Crear links**
-	**Delete Items**

[(Up)](#Table-of-Contents)

## 6: Apply

This button is responsible for applying the selected proposal. Once we click on **Apply** , the dialog closes and the proposed actions are executed.

[(Up)](#Table-of-Contents)

## 7: Exit

Closes the dialog box without taking any action.

[(Up)](#Table-of-Contents)

## Example multiplicities

Suppose we have an instance with an object of each class:

<img src="imgREADME/06_02_Multi01.png">

The **AbstractMachine** class is an abstract class that cannot be created directly by an object.

We note that **Multiplicities** is **Incorrect**.

If we click on the **Incorrect** button to access the **Wizard Association** screen, we will see that it indicates that the **grinder1** object is not connected to any **Part** object and therefore the **Uses** association fails.

<img src="imgREADME/06_03_Multi_ex01.png">

We also see that one of the proposals is to assign **Part1** (since it is not associated), create 3 objects of type **Part** and insert a link between **grinder1**, the **part1** object and the new (**NEWS**) objects that it creates.

If we select this option and click on **Apply**, we will get the following diagram of objects:

<img src="imgREADME/06_04_Multi_ex02.png">

We can see that the topic of multiplicities is still in an Incorrect state.

We can click on that button again to continue with the solution of these multiplicities and we see that there are fewer to solve.

This time, multiplicity fails because the object **cutter1** is not connected properly.

<img src="imgREADME/06_05_Multi_ex03.png">

Similar to the previous case, we will accept the creation of **4 objects** of type **Part** and the creation of the link of the same (**NEWS**) with **cutter1**.

Click on **Apply** and we will get the following diagram of objects:

<img src="imgREADME/06_06_Multi_ex04.png">

We can see how the problem of multiplicities has already been solved.

# Actions
This button allows access to MVM Wizard Actions. This utility is responsible for managing the record of the actions performed on a given instance. In this way, we can record each action and return to a certain point in the sequence in case we want to undo any of them. It is also possible to store all actions with a name so that you can retrieve it later and replay them all at once instantly.

Next, the main screen is shown and its graphic elements are commented on.

<img src="imgREADME/03_01_ActionsMain.png">

[(Up)](#Table-of-Contents)

## 1: File Name

Name of the file that will store our sequence of actions. This type of file is stored with the .mva extension.

## 2: Creation Date

Date and time of file creation .

## 3: Mod. Date

Date and time of the last modification of the file.

## 4: Model

Model on which the actions have been carried out.

## 5: Source USE File

File used in the MVM session and containing the model on which the actions have been performed.

## 6: Description

Description of the sequence of actions.

[(Up)](#Table-of-Contents)

## 7: Actions

Actions performed on the instance listed in the order they were performed.

<img src="imgREADME/03_02_ActionsTable.png">

The types of actions are as follows:

| **Abbrev** | **Meaning**            |
|------------|-------------------------|
| **CO**     | Create object           |
| **CL**     | Create link             |
| **DO**     | Delete object           |
| **DL**     | Delete link             |
| **MA**     | Modification object     |

When an action is selected, the **Objects** and **Links** blocks are synchronized to show the objects and links that exist after the action is performed.

We can check the elements that are created by clicking on the first 3 actions:

| **Actions** | **Links** |
|------------|-----------|
| 1 | <img src="imgREADME/03_03_ActionsSeq1.png"> |
| 2 | <img src="imgREADME/03_04_ActionsSeq2.png"> |
| 3 | <img src="imgREADME/03_05_ActionsSeq3.png"> |

[(Up)](#Table-of-Contents)

## 8: Objects

Displays existing objects after the selected action has been performed. When you select an object, the **Attributes block**  displays the values associated with each attribute of the object:

<img src="imgREADME/03_06_ActionsObjAttrs.png">

[(Up)](#Table-of-Contents)

## 9: Attributes

Displays the value of each of the attributes of the object that is selected. See figure shown in the previous section (8: Objects).

## 10: Open actions

This button allows you to open a file of sequences of actions.

<img src="imgREADME/03_07_ActionsFileOpen.png">

[(Up)](#Table-of-Contents)

## 11: Find Actions

<img src="imgREADME/03_10_ActionsLaunchFind.png">

This button allows you to search for files with sequences of actions: 

<img src="imgREADME/03_08_ActionsFindActions.png">

By default, it uses the model’s name to filter the files to be searched, but if we uncheck the **Filter model 'Animals'** check, it shows all the existing files:

<img src="imgREADME/03_09_ActionsFindActionsAll.png">

To load a file, just click on the line that contains it and click on the Load action button or double-click on that line.

[(Up)](#Table-of-Contents)

## 12: Save actions

It allows you to save a file with the actions carried out so far on the instance.

<img src="imgREADME/03_11_ActionsSaveFile.png">

[(Up)](#Table-of-Contents)

## 13: Load actions

This button allows you to create an instance with the elements indicated in the associated action. If a list of actions has for example 10 actions, but we select action 3, only the first 3 actions will be executed. This allows you to roll back the instance's situation to a certain point by undoing all subsequent instances.

<img src="imgREADME/03_13_ActionsLoad02.png">

[(Up)](#Table-of-Contents)

## 14: Links

Displays the existing links in the instance after the execution of the selected action.

<img src="imgREADME/03_15_ActionsLinks.png">

[(Up)](#Table-of-Contents)

## 15: Exit

Closes the dialog box.

[(Up)](#Table-of-Contents)

# Suggest fixes

Using this button, we make a query to OpenAI asking it mainly to help us determine what errors the model may contain and to tell us how we could solve it.

In the consultation we may provide you with certain information such as **INPUT** in case we have already calculated or not the **MUS**/**MSS** previously or we already have a collection of objects and links.

To provide **OpenAI** with the necessary context, the query will be performed with a block of text with the following structure:
-	**PROFILE**: contextualiza a OpenAI
-	**TASK**: lists the actions to be performed
-	**INPUTS**: information we provide to you
-	**OUTPUTS**: information we expect to receive and the required format
-	**REMARKS**: Considerations for refining your query

With this structure, we provide **OpenAI** with context, a set of tasks to perform, a set of information to analyze, and request an output to show to the designer and to perform other actions, such as creating a new instance as a result of the query. Obviously, we refined our query by adding additional instructions that improve the final answer.

Below, we detail each of the blocks that make up the query.

## Profile 

```
First, we contextualize OpenAI and indicate what its main role will be in this consultation.
We indicate the following:
**1**. You are a software modeling assistant, expert on software design, development and debugging.
**2**. You provide concise, concrete and actionable feedback about software design errors.
```


-------------

# ACKNOWLEDGMENT
Special thanks to ***Robert Clarisó*** for his invaluable help and perseverance and to ***Jordi Cabot*** for his many advices and very important suggestions.

# CITATION

Juan Antonio Gómez-Gutiérrez, Robert Clarisó.
Interactive Repair of Inconsistencies in Conceptual Models. 
In Proc. 44th International Conference on Conceptual Modeling (ER'2025). Lecture Notes in Computer Science, to appear, Springer.

https://link.springer.com/chapter/10.1007/978-3-032-08623-5_1

Juan Antonio Gómez-Gutiérrez, Robert Clarisó, Jordi Cabot.
A Tool for Debugging Unsatisfiable Integrity Constraints in UML/OCL Class Diagrams.
In Proc. 27th International Working Conference on Exploring Modeling Methods for Systems Analysis and Development (EMMSAD’2022). Lecture Notes in Business Information Processing vol. 450, pp. 267–275, Springer.

https://link.springer.com/chapter/10.1007/978-3-031-07475-2_18

   
# REFERENCES

* **Eclipse** - https://www.eclipse.org/downloads/
* **GitHub**  - https://desktop.github.com/
* **USE**     - https://github.com/useocl/use/

[(Up)](#Table-of-Contents)
