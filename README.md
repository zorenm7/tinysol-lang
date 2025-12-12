# tinysol-lang

An OCaml interpreter and typechecker for a tiny fragment of Solidity

## Installation

Install [opam](https://opam.ocaml.org/doc/Install.html), the OCaml official package manager. Assuming you're working on Ubuntu:
```bash
sudo apt install opam
```
Then, you must initialize opam. This installs OCaml and creates a default switch:
```bash
opam init --bare -a -y
```
Here we assume you will work on the default switch. To check that a switch actually exists:
```bash
opam switch list
```
In case the previous command shows an empty list, you must manually create a switch:
```bash
opam switch create tinysol ocaml-base-compiler
```
This creates a switch with the most up-to-date version of the OCaml compiler.

The following command updates environment variables, to make OCaml commands available on the current switch:
```bash
eval $(opam env)
```

Finally, install the OCaml packages:
```bash
opam install -y dune ocaml-lsp-server odoc ocamlformat utop menhir ppx_inline_test
```
In particular, this installation includes:
- [**dune**](https://dune.readthedocs.io/), a build system for OCaml projects, similar to make;
- [**utop**](https://opam.ocaml.org/blog/about-utop/), a REPL interface for OCaml;
- [**Menhir**](http://gallium.inria.fr/~fpottier/menhir/), a parser generator;
- [**ppx_inline_test**](https://github.com/janestreet/ppx_inline_test), a tool for writing in-line tests in OCaml.

## Usage

To build the project, run:
```bash
dune build
```

To run unit tests:
```bash
dune test
```

You can specify unit tests for a specific contract. For instance, consider the sample [Bank](test/contracts/Bank.sol) contract:
```solidity
//SPDX-License-Identifier: UNLICENSED
pragma solidity >= 0.8.2;

contract Bank {
    mapping (address user => uint credit) credits;

    function deposit() public payable {
        credits[msg.sender] += msg.value;
    }

    function withdraw(uint amount) public {
        require(amount > 0);
        require(amount <= credits[msg.sender]);

        credits[msg.sender] -= amount;

        payable(msg.sender).transfer(amount);
    }
}
```
A possible unit test for our contract is the following [Bank.t](test/contracts/Bank.t):
```
faucet 0xA 100
faucet 0xB 100
deploy 0xA:0xC() "test/contracts/Bank.sol"

0xA:0xC.deposit{value:20}()
assert 0xA this.balance==80
assert 0xC this.balance==20

0xB:0xC.deposit{value:30}()
assert 0xA this.balance==80
assert 0xB this.balance==70
assert 0xC this.balance==50

revert 0xA:0xC.withdraw(21)

0xA:0xC.withdraw(15)
assert 0xA this.balance==95
assert 0xB this.balance==70
assert 0xC this.balance==35
```

To run this unit test:
```bash
dune exec tinysol unittest test/contracts/Bank.t
```
The output is the following:
```
accounts: []                        
--- faucet 0xA 100 --->
accounts: [0xA -> { balance=100; } ]
--- faucet 0xB 100 --->
accounts: [0xB -> { balance=100; } 0xA -> { balance=100; } ]
--- deploy 0xA:0xC.constructor{value: 0}() test/contracts/Bank.sol --->
accounts: [0xC -> { balance=0; credits=<map>; } 0xB -> { balance=100; } 0xA -> { balance=100; } ]
--- 0xA:0xC.deposit{value: 20}() --->
accounts: [0xC -> { balance=20; credits=<map>; } 0xB -> { balance=100; } 0xA -> { balance=80; } ]
--- 0xB:0xC.deposit{value: 30}() --->
accounts: [0xC -> { balance=50; credits=<map>; } 0xB -> { balance=70; } 0xA -> { balance=80; } ]
--- revert 0xA:0xC.withdraw{value: 0}(21) --->
accounts: [0xC -> { balance=50; credits=<map>; } 0xB -> { balance=70; } 0xA -> { balance=80; } ]
--- 0xA:0xC.withdraw{value: 0}(15) --->
accounts: [0xC -> { balance=35; credits=<map>; } 0xB -> { balance=70; } 0xA -> { balance=95; } ]
--- 0xB:0xC.withdraw{value: 0}(30) --->
accounts: [0xC -> { balance=5; credits=<map>; } 0xB -> { balance=100; } 0xA -> { balance=95; } ]
```
