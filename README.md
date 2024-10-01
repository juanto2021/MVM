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
