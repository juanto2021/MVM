# MVM (Model Validator Mixer)


This project is a extension of the USE Model Validator plug-in from Martin Gogolla, Fabian Büttner, and Mark Richters 
for the UML-Based Specification Environment (http://useocl.sourceforge.net/w/index.php/Main_Page).
The code is developed in Java as an Eclipse plug-in. The output ".jar" file can be added as a plugin for USE v.0. 

Author: ***Juan Antonio Gómez Gutiérrez(2022)***

----
# Instructions for installation and testing


In order to test **MVM** you need to have **Eclipse IDE for Java Developers** (e.g. 2020-12 (4.18.0)) and download the following projects:

* **MVM**       - https://github.com/juanto2021/MVM.git<BR>
* **Use**       - https://github.com/juanto2021/JuantoUse.git<BR>
* **Usecompi**  - https://github.com/juanto2021/JuantoUseCompi.git<BR>

Once downloaded in the same workspace, locate the `build.xml` file of the **MVM project** and make sure that the following properties are well defined:

```html
...
<property name="use.path" value="..\..\JuantoUseCompi\usecompi" />

...

<target name="deployDebug" depends="jar"\>

  <copy file="dist/${filename}" todir="${use.path}/lib/plugins"/\>
  
  <copy file="dist/${filename}" todir="../../JuantoUse/use/lib/plugins"/\>
  
</target\>
```

Next, select the use `[JuantoUse main]` project and create a **Debug configuration** by defining the following values in Main:

>***Project:***    **use**

>***Main class:*** **org.tzi.use.main.Main**


Click on the Debug button and select:

>***File->Open Specification***

>***..\use\examples\Others\Juanto\Animals.use***

The first time you run the utility, you must also configure the properties through the **Plugins->Model Validator->Configuration** option to the following values:
  
>Check `Integer` and define **Minimum: -10** y **Maximum: 10**
  
>Check `String` and define **Min. Div. Values: 0** y **Max. Div. Values: 10**
  
Press Validate and verify that through the 'standard' validation of **USE**, the model is ***UNSATISFIABLE***.
  
To run MVM, use the **Plugins->ValidationMVM->ValidationMVM** option or locate the green icon containing an uppercase `M`.
  
At this point you will already see a dialog box with the tabs:

## Errors 

![](https://github.com/juanto2021/MVM/blob/main/img02.png)
    
In this tab, we show the minimal combinations of invariants that are unsatisfiable (minimal unsatisfiable cores). It consists of the following panels:
  
* ***Faulty combinations:*** The leftmost panel shows the minimal unsatisfiable core. When a combination is selected in this list, the following two views are synchronized.
  
* ***Example instances without the selected invariant:*** This panel shows examples of satisfiable combinations that do not contain one invariant from the core. Double-clicking a combination (each excludes one invariant from the core) creates an object diagram that satisfies the invariant in that combination.
  
* ***OCL for inv:*** For convenience, this panel displays the OCL definition of the selected invariant.
 
## Best approximate solutions 
    
![](https://github.com/juanto2021/MVM/blob/main/img05.png)
    
This tab shows the satisfiable combinations with the highest number of invariants:
  
* ***Invariants:*** The leftmost panel shows the list of satisfiable combinations with the highest number of invariants.
  
* ***Combination panel:*** When clicking on a combination, the invariants that compose it are shown in the upper right panel.
  
* ***OCL for inv:*** When clicking on a specific invariant, the definition of that invariant is shown in the lower panel.
  
## Statistics 

![](https://github.com/juanto2021/MVM/blob/main/img06.png)
    
The computation of unsatisfiable cores relies on USE’s Model Validator to check if a given combination of invariants is satisfiable or not. If a combination of invariants is deemed unsatisfiable, supersets of this combination will also be unsatisfiable. Similarly, if a combination is found to be satisfiable, it is not necessary to explore subsets of this combination. Thus, it is not necessary to invoke the Model Validator for each combination: many calls can be pruned.

  This tab shows information about the computation of unsatisfiable cores and sample instances. It describes the CPU time spent searching for combinations, the number of calls to the solver, and the number of calls that produced a satisfiable/unsatisfiable result.

## ACKNOWLEDGMENT
Special thanks to ***Robert Clariso*** for his invaluable help and perseverance and to ***Jordi Cabot*** for his many advices and very important suggestions.

## CITATION

Work on this tool has been published in the paper: 
"A Tool for Debugging Unsatisfiable Integrity Constraints in UML/OCL Class Diagrams". J. A. Gómez, R. Clarisó, J. Cabot. EMMSAD'2022. LNCS, Springer. To appear.

   
## REFERENCES

* **Eclipse** - https://www.eclipse.org/downloads/
* **GitHub**  - https://desktop.github.com/
* **USE**     - http://useocl.sourceforge.net/w/index.php/Main_Page
