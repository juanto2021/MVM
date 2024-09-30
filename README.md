# MVM (Model Validator Mixer - - )


This project is a extension of the USE Model Validator plug-in from Martin Gogolla, Fabian Büttner, and Mark Richters 
for the UML-Based Specification Environment (https://sourceforge.net/projects/useocl/). The code is developed in Java.

Author: ***Juan Antonio Gómez Gutiérrez(2024)***

----
# Instructions for full installation


To test **MVM** you need to have **Eclipse IDE for Java developers** (e.g. 2020-12 (4.18.0)) and download the following projects:

|Repository    |URL                                            |
|:-------------|:----------------------------------------------|
|**MVM**   	   |https://github.com/juanto2021/MVM.git          |
|**Use**	     |https://github.com/juanto2021/MVMUse.git     |
|**Usecompi**	 |https://github.com/juanto2021/MVMUseCompi.git|



Once downloaded to the same workspace, locate the **MVM project's** 'build.xml' file  and make sure the following properties are well defined:

```html
...
<property name="use.path" value="..\..\MVMUseCompi\usecompi" />
...
<target name="deployDebug" depends="jar"\>
  <copy file="dist/${filename}" todir="${use.path}/lib/plugins"/\>
    <copy file="dist/${filename}" todir="../../MVMUse/use/lib/plugins"/\>
  </target\>
```

Next, select the use '[MVMuse main]' project and create a Debug Configuration by setting the following values to Main:

![](https://github.com/juanto2021/MVM/blob/main/01_Config.png)

Click the **Debug** button and then, open the **shop.use** definition file:

![](https://github.com/juanto2021/MVM/blob/main/02_Open_Specification.png)

The first time you run the utility, you must also configure the properties through the **Plugins->Model Validator->Configuration** option to the following values:
  
![](https://github.com/juanto2021/MVM/blob/main/03_Shop_Properties.png)
  
Press Validate and verify that through the 'standard' validation of **USE**, the model is ***UNSATISFIABLE***.

# Instructions for minimal installation for testing

If you just want to try the tool, simply download the following compressed file:
https://drive.google.com/file/d/1LIwjN9ij4VgNmRD4M1ZnvAnGz9txmMhd/view?usp=sharing
Once downloaded, we will extract it to the folder we consider appropriate (e.g. C:\Temp) and we will notice that the folder created after extraction has the following contents:

![](https://github.com/juanto2021/MVM/blob/main/04_Dir_MVM_Compact.png)

|Repository    |URL                                            |
|:-------------|:----------------------------------------------|
|**groupActions**   	   |Folder that will store the files with the action groups that we want to save.          |
|**jre**	     |JRE using the tool.     |
|**MVMUse**	 |Original USE content with the MVM-provided extension required for its execution.|



# Tool Description

# Case Study

## Launch Brute force

## Launch MVM Wizard & Object diagram

## Check Objects Satisfiability

## Create new Order_line

## Create new link

## Solving invariants with problems

### password_min_length

### distinctProductsInOrderLines

#### Delete link between orders_line2 and products1

#### Create a new product (products2)

#### Create a link between it and categories1

#### Create link between orders_line2 and products2

### calculate_total

### sufficient_stock

## Save actions

## Check invariants state

Put the rest of 'readme.md'

UNDER CONSTRUCTION

## ACKNOWLEDGMENT
Special thanks to ***Robert Clariso*** for his invaluable help and perseverance and to ***Jordi Cabot*** for his many advices and very important suggestions.

## CITATION

Work on this tool has been published in the paper: 
"A Tool for Debugging Unsatisfiable Integrity Constraints in UML/OCL Class Diagrams". J. A. Gómez, R. Clarisó, J. Cabot. EMMSAD'2022. LNCS, Springer. To appear.

   
## REFERENCES

* **Eclipse** - https://www.eclipse.org/downloads/
* **GitHub**  - https://desktop.github.com/
* **USE**     - http://useocl.sourceforge.net/w/index.php/Main_Page
