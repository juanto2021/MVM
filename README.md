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
