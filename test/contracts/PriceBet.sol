//SPDX-License-Identifier: GPL-3.0-only
pragma solidity >= 0.8.2;

contract PriceBet {
    uint initial_pot;        // pot transferred from the owner to the contract
    uint deadline;           // a time limit after which the player loses the bet
    uint exchange_rate;      // target exchange rate that must be reached in order for the player to win the bet.      
    address oracle;          // contract queried for the exchange rate between two given tokens
    address payable owner;
    address payable player;

    constructor(address _oracle, uint _timeout, uint _exchange_rate) payable {
        require (msg.value > 0);
        initial_pot = msg.value;
        owner = payable(msg.sender);
        oracle = _oracle;
        deadline = block.number + _timeout;
        exchange_rate = _exchange_rate;
    }
   
    // join allows a player to join the bet. This requires the player to deposit an amount of ETH equal to the initial pot.
    function join() public payable {
        require(msg.value == initial_pot);
        require(player == "0x0");
        require(msg.sender != "0x0");

        // we require that join can only be performed before the deadline
        require(block.number < deadline);

        player = payable(msg.sender);
    }

    // win allows the joined player to withdraw the whole contract balance if the oracle exchange rate is greater than the bet rate. 
    // win can be called multiple times before the deadline. This action is disabled after the deadline
    function win() public {
        require(block.number < deadline);
        require(msg.sender == player);

        // Warning: at deployment time, we cannot know for sure that address oracle actually contains a deployment of contract Oracle
        Oracle oracle_instance;
        oracle_instance = Oracle(oracle);
        // require(oracle_instance.get_exchange_rate() >= exchange_rate);

        player.transfer(address(this).balance);
    }

    // // timeout can be called by anyone after the deadline, and transfers the whole contract balance to the owner
    function timeout() public {
        require(block.number >= deadline);

        owner.transfer(address(this).balance);
    }
}