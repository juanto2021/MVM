# MVM (Model Validator Mixer - - )

## Índice
- [Introduction](#Introduction)
- [Instructions for full installation](#Instructions for full installation)
- [Instructions for minimal installation for testing](#Instructions for minimal installation for testing)

# Introduction

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
|**wrkReplaceBodyInv**	 |MVM Toolkit for Compute and Storage of Invariant Alternatives.|
|**command_use_Runtime.bat**	 |Batch process running MVM.|
|**shop.properties**	 |Properties defined to test the sample model.|
|**shop.use**	 |Definition of the example model.|

To run the application, double-click on the file:

```
command_use_Runtime.bat
```
A CMD window will open:

![](https://github.com/juanto2021/MVM/blob/main/05_CMD.png)

Next, we'll see the application running:

![](https://github.com/juanto2021/MVM/blob/main/06_MVM_Wizard.png)


# Tool Description

MVM offers a variety of capabilities to help detect inconsistencies in your models and correct them based on various suggestions based on object creation and association links.
-	Search for the  Minimal Unsatisfiable Subsets (MUS) and Maximum Satisfiable Subsets (MSS)
-	Creation of objects and links between objects according to the associations involved.
-	Displaying such creation in an  object diagram
-	Check for invariant compliance  for each object
-	Checking the structure according to associations
-	Action history  that allows you to save and retrieve a set of actions

## Model

```
model shop

-- Definition of the Products class
class Products 
    attributes
        ID: Integer
        description: String
        price: Real
        stock: Integer
end

-- Definition of the Categories class
class Categories 
    attributes
        ID: Integer
        name: String
end

-- Definition of the Customers class
class Customers 
    attributes
        ID: Integer
        name: String
        email: String
        pwd: String
        blocked: Integer
end

-- Definition of the Orders class
class Orders 
    attributes
        ID: Integer
        total: Real
end

-- Definition of the Orders_line class
class Orders_line 
    attributes
        quantity: Integer
end

-- Association between Orders and Customers
association OrderCustomer between
    Orders[*] role order
    Customers[1] role customer
end

-- Association between Orders_line and Orders
association OrderLineOrder between
    Orders_line[1..*] role orderLine
    Orders[1] role order
end

-- Association between Products and Categories
association ProductCategory between
    Products[*] role product
    Categories[1] role category
end

-- Association between Orders_line and Products
association OrderLineProduct between
    Orders_line[*] role orderLine
    Products[1] role product
end

constraints

-- Constraints block

-- Invariants for Products
context Products inv ID_positive:
    self.ID > 0

context Products inv description_not_empty:
    self.description.size() > 0

context Products inv price_non_negative:
    self.price >= 0.0

context Products inv stock_non_negative:
    self.stock >= 0

context Products inv stock_reasonable:
    self.stock <= 10000

context Products inv unique_product_id:
    Products.allInstances()->forAll(p | p <> self implies p.ID <> self.ID)

context Products inv sufficient_stock:
    self.stock = Orders_line.allInstances()
                    ->select(ol | ol.product = self)
                    ->collect(ol | ol.quantity)
                    ->sum()

-- Invariants for Categories
context Categories inv ID_positive:
  self.ID > 0

context Categories inv name_not_empty:
  self.name.size() > 0

context Categories inv name_unique:
  Categories.allInstances()->forAll(c | c <> self implies c.name <> self.name)

context Categories inv name_valid_length:
  self.name.size() <= 50
  
-- Invariants for Customers
context Customers inv ID_positive:
    self.ID > 0

context Customers inv name_not_empty:
    self.name.size() > 0

context Customers inv password_min_length:
    self.pwd.size() >= 8

context Customers inv blocked_status:
    self.blocked >= 0 and self.blocked <= 1

context Customers inv customer_not_blocked:
    self.order->notEmpty() implies self.blocked = 0
  
-- Invariants for Orders
context Orders inv ID_positive:
    self.ID > 0

context Orders inv customer_assigned:
    self.customer->notEmpty()

context Orders inv unique_order_id:
    Orders.allInstances()->forAll(o | o <> self implies o.ID <> self.ID)

context Orders inv calculate_total:
    self.total = self.orderLine
       ->collect(ol | ol.quantity * ol.product.price)
       ->sum()

context Orders inv distinctProductsInOrderLines:
    self.orderLine->forAll(ol1, ol2 | ol1 <> ol2 implies ol1.product <> ol2.product)

```

![](https://github.com/juanto2021/MVM/blob/main/07_Class_Diagram_Shop.png)

## Main window

The listed functionalities are offered from several screens that are accessed from the following main screen:

![](https://github.com/juanto2021/MVM/blob/main/08_Main_Window.png)

To continue with the explanation, we can use the 'Fill' option and create an object from each of the classes. The panels are synchronized so that selecting a class displays its existing objects, and selecting an object displays its corresponding attributes and values.

## Multiplicities

If we click on **Multiplicities**, we access the following screen:

![](https://github.com/juanto2021/MVM/blob/main/09_W_Wizard_Association.png)

This screen shows the existing associations and for each of them, the links created so far with information on connections, multiplicities, etc. that show a problem to be solved. At the bottom, actions are proposed to automatically resolve the problems associated with the link that we find previously selected in the **Links** table. Once a proposal has been selected, when we return to the main screen we will see the actions that have been carried out, such as the creation of objects and their assignment to establish links in an association:

![](https://github.com/juanto2021/MVM/blob/main/10_W_Object_Diagram.png)

## Verify Object Satisfiability

To check the satisfiability of the invariants in each of the existing objects, you can access the Check Satisfiability Object of MVM window by clicking on the OBJs button that is in red indicating the existence of a problem:

![](https://github.com/juanto2021/MVM/blob/main/11_W_Objects_Satisfiability.png)

On this screen we can filter which objects have a problem and which invariant are not met in each case. When selecting an object, we can also see an auxiliary table where the expressions of each invariant are shown to facilitate comparison with the naked eye.

## Actions wizard

MVM records each of the actions performed (creation, modification and deletion of objects and links) in order to store collections of actions and retrieve them later to reproduce a certain situation. To access the management of these groups of actions we can click on the Actions button:

![](https://github.com/juanto2021/MVM/blob/main/12_W_Wizard_Actions.png)  

On this screen we can save and/or retrieve groups of actions and within each group we can select a specific action to recreate all the objects and links that are displayed after the completion of that action. In this way we can reconstruct a situation over and over again easily and quickly.

# Case Study

This case study is based on a very simple model in which customers can place orders made up of several detail lines. The model contains several invariants for each class in which certain characteristics of the same can be controlled, such as the uniqueness of **ID's**, positive values for **ID's**, or controls such as that the total of an order coincides with the **sum** of  the product of **quantity * price** of the detail lines of the same or that it is stock of a product matches the sum of quantities of the same ordered product on all  detail lines. 
To simplify the explanation, we omitted all the classic management of partial requests, modifications and cancellations of orders since the simple example proposed is enough to detail the functionalities of the tool.


## Launch Brute force
To test the tool, we can load the '**shop**' model into **USE** and then run the search for combinations for example using the '**Brute force**' method:

![](https://github.com/juanto2021/MVM/blob/main/13_Launch_Brute_Force.png)

After you run this option, a dialog box with the search results will be displayed. If we look at the '**Best approximate solutions**' tab, we will see that it shows a group of invariants that allow us to make the model satisfactory:

![](https://github.com/juanto2021/MVM/blob/main/14_Resultado_Brute_Force.png)


## Launch MVM Wizard & Object diagram

Double-clicking on the line that contains this group (top-left panel) will cause the Wizard to open for the processing of objects and links, and an object diagram will also be displayed with the result of the previous search:

![](https://github.com/juanto2021/MVM/blob/main/15_W_Pral.png)

In this case, we see that all the necessary links have been satisfied so that the 'multiplicities' section is displayed without problems.

## Check Objects Satisfiability

If we click on the **OBJs** button to see which invariants are met or not, the '**Check Objects Satisfiability**' dialog will appear showing the status of all the invariants so that we can start making decisions:

![](https://github.com/juanto2021/MVM/blob/main/16_W_Check_Objects_Satisfiability.png)

Analysing in a little more detail, we see that the invariants that fail are the following:

![](https://github.com/juanto2021/MVM/blob/main/17_W_COS_Fail01.png)

That is, in the **customers1** object, it fails because it does not have a  **long enough pwd** (**password_min_length**) and **orders1** (**calculate_total**) fails because the order total (**total = 2.0**) does not match the **sum of price*quantity of orders_line (2.0*10=20.0)**. 


## Create new Order_line

To make a richer example, we're going to add one more detail line to the current order. To do this, we close this dialog by clicking on the Exit button and, once on the main screen of the Wizard, we will select '**Orders_line**' from the list of classes and create a new one automatically by simply clicking on the '**+**'  button:

![](https://github.com/juanto2021/MVM/blob/main/18_W_Add_orderline.png)

After creating the new object, we can see how it has been added to the object diagram and how the states relative to multiplicities and the state of invariants have changed so that now, the instance of this model is unsatisfiable:

![](https://github.com/juanto2021/MVM/blob/main/19_W_After_Add_orderline.png)

## Create new link

Because the new **order_line2** requires a product, we could either associate the existing product (**products1**) or create a new one. To test the link building functionality, we're going to manually associate **products1** with **orders_line2**. To do this, we will select the association '**OrderLineProduct**', then in the **From** drop-down of **Object->Orders_line** we will select **orders_line2**. Then in the **To** drop-down of **Products**, we will select products1 and finally click on **Insert Link**:

![](https://github.com/juanto2021/MVM/blob/main/20_W_Add_Link_orderline_products01.png)

Similarly, we will create a link between **orders1** and **orders_line2** by selecting the classes and objects corresponding to the new link we want to create and clicking on '**Insert Link**':

![](https://github.com/juanto2021/MVM/blob/main/21_W_Add_Link_orderline2_orders1.png)

After the creation of this last link, we see how the multiplicities have been solved and reorganizing the object diagram, we will see a result similar to the following:

![](https://github.com/juanto2021/MVM/blob/main/22_W_Add_Link_orderline2_orders1_diagram.png)



## Solving invariants with problems

If we click on the **OBJs** button to see which invariants fail, we will see that the following ones fail:

![](https://github.com/juanto2021/MVM/blob/main/23_W_Invs_fail01.png)


### password_min_length

To start to solve problems, we'll close the dialog by pressing the **Exit** button   and move on to modifying the **customers1** pwd. In the main window of the wizard, select the **Customers** class, the **customer1** object and, after modifying the **password** to enter for example '**my_password**' we will click on the **Save Obj** button:

![](https://github.com/juanto2021/MVM/blob/main/24_W_Modify_pwd.png)


### distinctProductsInOrderLines

Next, we see that the invariant 'distinctProductsInOrderLines' forces us to have different products in the same order and that our lines (1 and 2) use the same product (products1). To resolve this, we need to perform the following actions:
-	Borrar link entre orders_line2 y products1
-	Create a new product (products2)
-	Create a link between it and categories1
-	Crear link entre orders_line2 y products2


#### Delete link between orders_line2 and products1

![](https://github.com/juanto2021/MVM/blob/main/25_W_delete_line_orders_line2_products1.png)

#### Create a new product (products2)

![](https://github.com/juanto2021/MVM/blob/main/26_W_Create_products2.png)

#### Create a link between it and categories1

![](https://github.com/juanto2021/MVM/blob/main/27_W_insert_products2_categories1.png)

#### Create link between orders_line2 and products2

![](https://github.com/juanto2021/MVM/blob/main/28_W_insert_products2_orders_line2.png)

### calculate_total

To solve this invariant, simply modify the total **orders1** attribute  and assign it the value of **50**,  which is the sum of the **product quantity*price** of all the lines of **order_lines**:

![](https://github.com/juanto2021/MVM/blob/main/29_W_modif_total.png)

### sufficient_stock

If we click on the **OBJs** button to see how we have been solving problems, we will see that we have indeed only one left to solve:

![](https://github.com/juanto2021/MVM/blob/main/30_W_stock01.png)

The **current body** of the invariant is as follows:
```
(self.stock = Orders_line.allInstances->select(ol : Orders_line | (ol.product = self))
     ->collect(ol : Orders_line | ol.quantity)->sum)
```
Coincidentally, we see in the example that this expression is **true** for **orders_line1** since its **quantity** is **10** and the stock of **products1** is also **10**. However, we see that it is **not true** for **orders_line2** since its **quantity** is **10** but the stock of **products2** is **5**.
Normally, the stock of a product would always be higher than the total of the existing detail lines in all **order**s so that they can be served without problems.
If we look at the '**Body alternatives**' block, we see that one of the proposed alternatives is indeed the one we assume to be 'ideal':

```
(self.stock <= Orders_line.allInstances->select(ol : Orders_line | (ol.product = self))
     ->collect(ol : Orders_line | ol.quantity)->sum)
```
If we select that alternative, we see how the 'New Invariant body' block shows a correct result:

![](https://github.com/juanto2021/MVM/blob/main/31_W_alt_stock.png)

Intuitively, we can notice that, if we type any **bodyexpression** in the text box associated with '**New Invariant body**' and click on the **Test** button, it will verify whether the text is a correct body or not.
At this point, if we wanted to make a copy of the current model where we replaced the current invariant with the new alternative, it would be enough to click on the **Save file** button and give a name to the destination file (e.g. **shop_v2.use**):

![](https://github.com/juanto2021/MVM/blob/main/32_W_save_file.png)

## Save actions

Finally, if we wanted to save all the actions carried out regarding the creation of objects and links, we would exit this dialog by clicking on the **Exit** button and in the main wizard window we would click on the **Actions** button:

![](https://github.com/juanto2021/MVM/blob/main/33_W_Actions01.png)

In the dialog that appears, we will simply give the file a name , enter a description (recommended) and click on **Save actions**:

![](https://github.com/juanto2021/MVM/blob/main/34_W_Save_Actions.png)

One way to check the whole process described so far would be to abandon the current model (**shop.use**) and recover the copy we have made in the example (**shop_v2.use**).
If we load **shop_v2.use** and invoke the wizard view, we can click on the **Actions** button to find the previously saved action file and finally load these actions to reproduce the changes made to get the desired objects, values and links to make almost the entire instance of the example satisfactory (except for the change of body expression for one of the proposed alternatives):

![](https://github.com/juanto2021/MVM/blob/main/35_W_Test_new_model.png)

## Check invariants state

Finally, we see how we have indeed managed to get all the checks correct and an object diagram correct.
If we click on the button with the text '**Correct**' in green that is associated with the '**State invariants**' label, we will see how all the invariants in show in green:

![](https://github.com/juanto2021/MVM/blob/main/36_W_AllInvsCorrect_ClassInvariants.png)

## ACKNOWLEDGMENT
Special thanks to ***Robert Clarisó*** for his invaluable help and perseverance and to ***Jordi Cabot*** for his many advices and very important suggestions.

## CITATION

Work on this tool has been published in the paper: 
"A Tool for Debugging Unsatisfiable Integrity Constraints in UML/OCL Class Diagrams". J. A. Gómez, R. Clarisó, J. Cabot. EMMSAD'2022. LNCS, Springer. To appear.

   
## REFERENCES

* **Eclipse** - https://www.eclipse.org/downloads/
* **GitHub**  - https://desktop.github.com/
* **USE**     - http://useocl.sourceforge.net/w/index.php/Main_Page
