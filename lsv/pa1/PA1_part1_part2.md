## PA1

### 1. [Using ABC]

#### (b)

1. visualize the network structure (command `show`) result

![](https://i.imgur.com/IarZHUV.png)

2. visualize the AIG (command `show`) result

![](https://i.imgur.com/09OYkYv.png)


3. visualize the BDD (command `show_bdd`) result

![](https://i.imgur.com/ckfzlDS.png)


### 2. [ABC Boolean Function Representations]

#### (a)

##### 1. `aig` vs. `strash`

`aig`: 將logic network中的local node轉為AIG。

`strash`: 利用one-level structural hashing將整個logic network轉成AIG。

以four-bit adder為例，在`aig`指令後`print_stats`會顯示`nd = 8`, `aig = 52` 表示它為一個logic network而local nodes是用AIG來表示。而在`strash`指令後`print_stats`則會顯示`and = 44`表示整個network已經轉成一個structurally hashed AIG。

##### 2. `bdd` vs. `collapse`


`bdd`: 將logic network中的local node轉為BDD。

`collapse`: 建構出的network每一個primary output會由一個BDD node來表示(每一個BDD node的fanout為其中一個primary output), 而BDD node的fanins皆為primary input。

以four-bit adder為例，在`bdd`指令後`print_stats`會顯示`nd = 8`, `bdd = 28` ，表示它為一個logic network而local nodes是用BDD來表示。而在`collapse`之後可以看到`nd = 5` 和primary output的個數一樣，若用`show`指令來觀察整個network的structure則可以發現每個node的fanout都對應到一個primary output, 而每個node的fanins皆為primary input。


#### (b)

可利用`logic`指令將structurally hashed AIG轉為node function由sum-of-products (SOP)表示的logic network。
