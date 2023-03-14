using DummyERC20A as ERC20a 
using DummyERC20B as ERC20b 

methods {
    name() returns string envfree;
    symbol() returns string envfree;
    decimals() returns uint8 envfree;
    asset() returns address envfree;

    totalSupply() returns uint256 envfree;
    balanceOf(address) returns uint256 envfree => DISPATCHER(true);
    nonces(address) returns uint256 envfree;

    approve(address,uint256) returns bool;
    transfer(address,uint256) returns bool => DISPATCHER(true);
    transferFrom(address,address,uint256) returns bool => DISPATCHER(true);
    deposit(uint256,address);
    mint(uint256,address);
    withdraw(uint256,address,address);
    redeem(uint256,address,address);

    totalAssets() returns uint256 envfree;
    userAssets(address) returns uint256 envfree;
    convertToShares(uint256) returns uint256 envfree;
    convertToAssets(uint256) returns uint256 envfree;
    previewDeposit(uint256) returns uint256 envfree;
    previewMint(uint256) returns uint256 envfree;
    previewWithdraw(uint256) returns uint256 envfree;
    previewRedeem(uint256) returns uint256 envfree;

    maxDeposit(address) returns uint256 envfree;
    maxMint(address) returns uint256 envfree;
    maxWithdraw(address) returns uint256 envfree;
    maxRedeem(address) returns uint256 envfree;

    permit(address,address,uint256,uint256,uint8,bytes32,bytes32);
    DOMAIN_SEPARATOR() returns bytes32;

    ERC20a.balanceOf(address) returns uint256 envfree;
    ERC20a.myAddress() returns address envfree;
}

definition MAX_UINT256() returns uint256 = 0xffffffffffffffffffffffffffffffff;


// multi contract call
// Property: any rounding error should be in favor of the system (system shoudn't lose)
rule dustFavorsTheHouse(env e, uint assetsIn, address receiver, address owner)
{
    require e.msg.sender != currentContract && receiver != currentContract;
    require totalSupply() != 0;

    uint balanceBefore = ERC20a.balanceOf(currentContract);

    uint shares = deposit(e, assetsIn, receiver);
    uint assetsOut = redeem(e, shares, receiver, owner);

    uint balanceAfter = ERC20a.balanceOf(currentContract);

    assert balanceAfter >= balanceBefore;
}



// ghost and hook
ghost mathint sumOfBalances {
    init_state axiom sumOfBalances == 0;
}

hook Sstore balanceOf[KEY address addy] uint256 newValue (uint256 oldValue) STORAGE {
    sumOfBalances = sumOfBalances + newValue - oldValue;
}

hook Sload uint256 val balanceOf[KEY address addy] STORAGE {
    require sumOfBalances >= val;
}

// invariant
// Property: system solvency (total supply is the sum of all balances)
invariant totalSupplyIsSumOfBalances(env e)
    totalSupply() == sumOfBalances



// last revert rule
// Property: if a deposit fails, the user's balance should not change
rule depositRevertsIfNoSharesMinted(env e) {
    uint256 assets; address receiver;
    uint256 sharesBefore = balanceOf(receiver); 

    require asset() != currentContract;

    deposit@withrevert(e, assets, receiver);
    bool isReverted = lastReverted;

    uint256 sharesAfter = balanceOf(receiver);

    assert sharesBefore == sharesAfter => isReverted, "Remember, with great power comes great responsibility.";
}

//Property transfer changes the balances correctlly
rule transferChangeBalancesCorrectly(env e, address receiver, uint amount) {
    
    uint maxUint = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff;

    uint256 balanceBefore = balanceOf(receiver);

    transfer(e, receiver, amount);

    uint256 balanceAfter = balanceOf(receiver);

    assert e.msg.sender != receiver && balanceBefore + amount <= maxUint => balanceAfter == balanceBefore + amount, "Transfer changed the amounts different than it should transfer";
    assert e.msg.sender == receiver &&  balanceBefore + amount <= maxUint => balanceAfter == balanceBefore, "If msg.sender send to itself no changes should be made";

}
// Variables transition
rule balanceOfModifiesOnlyBySomeFunctions(address user) {

    calldataarg args;
    method f;
    env e;
    uint256 sharesBefore = currentContract.balanceOf(user);
    

    f(e, args);
    
    uint256 sharesAfter =  currentContract.balanceOf(user);


    assert  sharesBefore != sharesAfter => (f.selector == deposit(uint,address).selector || 
    f.selector == mint(uint,address).selector ||
    f.selector == transfer(address,uint).selector ||
    f.selector == withdraw(uint,address,address).selector ||
    f.selector == redeem(uint,address,address).selector ||
    f.selector == transferFrom(address,address,uint).selector), "BalanceOf(user) modified on smth else";
}

rule balanceOfDecreasesOnlyBySomeFunctions(address user) {
    method f;
    env e;
    calldataarg args;
    require asset() != currentContract ;
    mathint sharesBefore = currentContract.balanceOf(user);
    // require (f.selector != mint(uint,address).selector && f.selector != deposit(uint,address).selector);
    if(f.selector == mint(uint,address).selector || f.selector == deposit(uint,address).selector) {
        uint amount;
        uint shares = mint(e,amount,user);
        uint shares1 = deposit(e,amount,user);
        require sharesBefore + shares <= MAX_UINT256();
        require sharesBefore + shares1 <= MAX_UINT256();
    } else {
        f(e, args);
    }
   
    mathint sharesAfter = currentContract.balanceOf(user);


    assert sharesBefore > sharesAfter => (f.selector == redeem(uint,address,address).selector ||
    f.selector == withdraw(uint,address,address).selector ||
    f.selector == transfer(address,uint).selector ||
    f.selector == transferFrom(address,address,uint).selector), "BalanceOf(user) decrease by other functions"; 
}


rule balanceOfIncreaseOnlyBySomeFunctions(address user) {

    
    method f;
    env e;
    calldataarg args;
    require asset() != currentContract;
    uint256 sharesBefore = currentContract.balanceOf(user);
    f(e, args);
    uint256 sharesAfter =  currentContract.balanceOf(user);
    
    assert  sharesBefore < sharesAfter => (f.selector == deposit(uint,address).selector || 
    f.selector == mint(uint,address).selector ||
    f.selector == transfer(address,uint).selector ||
    f.selector == transferFrom(address,address,uint).selector), "BalanceOf(user) increased on smth else";
}


rule totalSupplyIncreasedByDeposit(env e, uint256 amount, address receiver) {

    uint256 totalSupplyBefore = totalSupply();
    


    deposit(e, amount, receiver);

    uint256 totalSupplyAfter = totalSupply();


    assert totalSupplyBefore <= totalSupplyAfter, "TotalSupply didn't increase on deposit";
}

rule totalSupplyIncreasedByMint(env e, uint256 amount, address receiver) {
    uint256 totalSupplyBefore = totalSupply();


    mint(e, amount, receiver);

    uint256 totalSupplyAfter = totalSupply();


    assert totalSupplyBefore <= totalSupplyAfter, "TotalSupply didn't increase on mint";
}

rule antiMonotonicity(env e, address user) {
    
    require asset() != currentContract;
    require e.msg.sender != currentContract && user != currentContract;
    require user == e.msg.sender;
    mathint assetContractBalanceBefore = totalAssets();
    mathint asssetUserBalanceBefore = userAssets(user);

    method f;
    calldataarg args;
    if(f.selector == redeem(uint,address,address).selector){
        uint amount;
        redeem(e,amount,user,user);
    } else if(f.selector == withdraw(uint,address,address).selector) {
        uint amount;
        withdraw(e,amount,user,user);
    } else {
        f(e, args);
    }


    mathint assetContractBalanceAfter = totalAssets();
    mathint asssetUserBalanceAfter = userAssets(user);

    assert assetContractBalanceBefore < assetContractBalanceAfter <=> asssetUserBalanceBefore > asssetUserBalanceAfter , "Asset balance are not antiMonotonicity";
    assert assetContractBalanceBefore != assetContractBalanceAfter <=> asssetUserBalanceBefore != asssetUserBalanceAfter ,"If one asset changes both should change";

}


//State transition
invariant totalSupplyIsGTZeroIfAssetsIsGTZero() 
    to_mathint(totalSupply()) > 0 => to_mathint(totalAssets()) > 0
     filtered {
        f -> f.selector != withdraw(uint,address,address).selector && f.selector != redeem(uint,address,address).selector
    }
    {
        preserved with(env e) {
            require e.msg.sender != currentContract;
            require asset() != currentContract;
        }
    }

invariant totalSupplyIsZeroIfAssetsIsZero() 
    totalSupply() == 0 <=> totalAssets() == 0
    {
        preserved with(env e) {
            require e.msg.sender != currentContract;
            require asset() != currentContract;
            require totalSupply() == totalAssets();
        }
        preserved redeem(uint amount, address user, address owner) with(env e2) {
            require user != currentContract;
            require owner != currentContract;
            require totalSupply() == totalAssets();
        }
       preserved withdraw(uint amount, address user, address owner) with(env e3) {
            require user != currentContract;
            require owner != currentContract;
            require totalSupply() == totalAssets();
       }
    }


// Risk assessement

rule noDoubleRedeem(address user) {
    require asset() != currentContract;
    uint256 amount = balanceOf(user);
    env e;
    require e.msg.sender == user;
    redeem(e,amount,user,user);
    uint256 x;
    redeem@withrevert(e,x,user,user);
    assert lastReverted;
}


//Valid state

invariant totalSupplyLTAssetOfContract()
    totalSupply() <= totalAssets()
    filtered {
        f -> f.selector != withdraw(uint,address,address).selector && f.selector != redeem(uint,address,address).selector
    }
    {
        preserved with(env e){
            require e.msg.sender != currentContract;
            require asset() != currentContract;
        }
    }
