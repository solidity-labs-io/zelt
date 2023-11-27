/// 1 munging --- change solidity code to write spec
/// 2 helpers --- exposing additional things and behaviors you don't have access to
/// 3 harnessing --- add solidity code to expose variables and make it play nice with the prover

methods {
    /// envfree
    function bufferCap() external returns (uint256) envfree;
    function midPoint() external returns (uint256) envfree;
    function rateLimitPerSecond() external returns (uint256) envfree;
    function MAX_RATE_LIMIT_PER_SECOND() external returns (uint256) envfree;
    function lastBufferUsedTime() external returns (uint256) envfree;
    function bufferStored() external returns (uint256) envfree;
}

function uint32Max() returns uint256 {
    return 2 ^ 32 - 1;
}

function uint112Max() returns uint256 {
    return 2 ^ 112 - 1;
}

function absDelta(mathint a, mathint b) returns mathint {
    if (a > b) {
        return a - b;
    }

    return b - a;
}

/// State Transitions

/// if depleting, amount <= buffer()
/// after depletion, buffer() == buffer() - amount
/// - lastBufferUsedTime == block.timestamp if amount != 0
/// - bufferStored == buffer()


/// if replenishing
/// - lastBufferUsedTime == block.timestamp if amount != 0 && bufferCap != newBuffer
/// - bufferStored() <= bufferCap

/// ----------------------
/// ----- Invariants -----
/// ----------------------

/// 1). buffer() <= bufferCap
/// 2). bufferStored <= bufferCap
/// 3). rateLimitPerSecond <= MAX_RATE_LIMIT_PER_SECOND
/// 4). midpoint < bufferCap
/// 5). midpoint == bufferCap / 2
/// 6). always converges on midpoint over time with non zero rate limit
/// 7). buffer <= uint112Max
/// 8). bufferCap <= uint112Max
/// 9). lastBufferUsedTime updated when non view function is called, when buffer is ne midpoint
/// 10). bufferStored changes when:
/////       1. rate limit ne 0
/////       2. buffer != midpoint
/////       3. lastBufferUsedTime != block.timestamp
/// 11). deplete: buffer -= amount
/// 12). replenish: buffer += amount
/// 13). setBufferCap: bufferStored <= bufferCap, (already covered by invariant #2)

/// 1). buffer() <= bufferCap
/// buffer must be non zero for this to work
invariant bufferLteBufferCap(env e)
    (bufferCap() != 0) => (buffer(e) <= assert_uint256(bufferCap())) {
        preserved {
            requireInvariant midPointLtBufferCap();
            requireInvariant bufferStoredLteBufferCap(e);
        }
    }

/// 2). bufferStored <= bufferCap
/// if buffercap is non-zero, bufferStored <= bufferCap
invariant bufferStoredLteBufferCap(env e)
    (bufferCap() > 0) => (to_mathint(bufferStored()) <= to_mathint(bufferCap())) {
        preserved {
            requireInvariant midPointLtBufferCap();
        }
    }

/// 3). rateLimitPerSecond <= MAX_RATE_LIMIT_PER_SECOND
invariant maxRateLimitPerSecond()
    to_mathint(rateLimitPerSecond()) <= to_mathint(MAX_RATE_LIMIT_PER_SECOND());

/// 4). midpoint < bufferCap
invariant midPointLtBufferCap()
    (bufferCap() > 0) => midPoint() < bufferCap() {
        preserved {
            requireInvariant midPointHalfBufferCap();
        }
    }

/// 5). midpoint == bufferCap / 2
invariant midPointHalfBufferCap()
    to_mathint(midPoint()) == to_mathint(bufferCap()) / 2;

/// 7). buffer <= uint112Max
invariant bufferLteUint112(env e)
    to_mathint(buffer(e)) <= to_mathint(uint112Max());

/// 8). bufferCap <= uint112Max
invariant bufferCapLteUint112()
    to_mathint(bufferCap()) <= to_mathint(uint112Max());

/// -------------------
/// ------ Rules ------
/// -------------------

/// last buffer used time monotonically increasing
rule lastBufferUsedTimeCorrectlyUpdated(env e, method f) filtered {
    f -> !f.isView
} {
    require ((2 ^ 32) - 1) >= e.block.timestamp; /// only allow timestamps less than or equal to 2^32 - 1

    calldataarg args;

    uint256 lastBufferUsedTimePre = lastBufferUsedTime();
    require to_mathint(lastBufferUsedTimePre) <= to_mathint(e.block.timestamp);

    f(e, args);

    uint256 lastBufferUsedTimePost = lastBufferUsedTime();

    assert lastBufferUsedTimePre <= lastBufferUsedTimePost, "incorrect state transition";
    assert to_mathint(lastBufferUsedTimePost) <= to_mathint(e.block.timestamp), "incorrect post timestamp set, cannot be in the future";
}

/// buffer does not change
rule noStateChanges(env e, method f) 
filtered {
    f ->
    f.selector != sig:sync().selector &&
    f.selector != sig:setBufferCap(uint112).selector &&
    f.selector != sig:setRateLimitPerSecond(uint128).selector &&
    f.selector != sig:replenishBuffer(uint256).selector &&
    f.selector != sig:depleteBuffer(uint256).selector
} {
    calldataarg args;

    uint256 lastBufferUsedTimePre = lastBufferUsedTime();
    uint256 bufferStoredPre = bufferStored();
    uint256 lastBufferPre = buffer(e);

    f(e, args);

    assert lastBufferUsedTimePre == lastBufferUsedTime(), "last buffer used time state change";
    assert bufferStoredPre == bufferStored(), "last buffer stored state change";
    assert lastBufferPre == buffer(e), "buffer state change";
}

rule timePassingBufferConvergesOnMidpoint(env e1, env e2) {
    mathint lastBufferEnv1 = to_mathint(buffer(e1));
    mathint lastBufferEnv2 = to_mathint(buffer(e2));

    /// e2 is ahead of e1
    /// only allow e2 timestamps less than or equal to 2^32 - 1
    /// last buffer used time is less than or equal to e1 timestamp
    /// buffers cannot be the same
    /// buffer converges on midpoint if midpoint is half of buffer cap, and rate limit is non zero
    assert (
        (lastBufferEnv1 != lastBufferEnv2) &&
        (e2.block.timestamp <= uint32Max()) &&
        (e1.block.timestamp < e2.block.timestamp) &&
        (lastBufferUsedTime() < e1.block.timestamp) &&
        to_mathint(midPoint()) == (to_mathint(bufferCap()) / 2) &&
        rateLimitPerSecond() != 0
    ) => (absDelta(lastBufferEnv1, midPoint()) > absDelta(lastBufferEnv2, midPoint())), "buffer not converging on midpoint";
}

rule lastBufferUsedTimeAlwaysMonotonicallyIncreasingDeplete(env e, uint256 amount) {
    uint256 lastBufferUsedTimePre = lastBufferUsedTime();

    require uint32Max() >= e.block.timestamp; /// only allow timestamps less than or equal to 2^32 - 1
    require to_mathint(lastBufferUsedTimePre) < to_mathint(e.block.timestamp);
    require amount <= buffer(e);

    depleteBuffer(e, amount);

    uint256 lastBufferUsedTimePost = lastBufferUsedTime();

    assert lastBufferUsedTimePost > lastBufferUsedTimePre, "buffer used time incorrect, should be greater than pre";
}

rule lastBufferUsedTimeAlwaysMonotonicallyIncreasingReplenish(env e, uint256 amount) {
    uint256 lastBufferUsedTimePre = lastBufferUsedTime();

    require uint32Max() >= e.block.timestamp; /// only allow timestamps less than or equal to 2^32 - 1
    require to_mathint(lastBufferUsedTimePre) < to_mathint(e.block.timestamp);
    require amount <= buffer(e);
    require to_mathint(buffer(e)) < to_mathint(bufferCap());

    replenishBuffer(e, amount);

    uint256 lastBufferUsedTimePost = lastBufferUsedTime();

    assert lastBufferUsedTimePost > lastBufferUsedTimePre, "buffer used time incorrect, should be greater than pre";
}

rule lastBufferUsedTimeMonotonicallyIncreasing(env e, method f)
filtered {
    f -> !f.isView
} {
    uint256 lastBufferUsedTimePre = lastBufferUsedTime();
    uint256 bufferPre = buffer(e);

    require uint32Max() >= e.block.timestamp; /// only allow timestamps less than or equal to 2^32 - 1
    require to_mathint(lastBufferUsedTimePre) < to_mathint(e.block.timestamp);

    calldataarg args;

    /// possible function calls:
    ///  - deplete buffer
    ///  - replenish buffer --- if already at bufferCap, no state changes
    ///  - setBufferCap
    ///  - setRateLimitPerSecond
    f(e, args);

    uint256 lastBufferUsedTimePost = lastBufferUsedTime();

    assert lastBufferUsedTimePost > lastBufferUsedTimePre, "buffer used time incorrect, should be greater than pre";
}

/// only converges when setting rate limit per second, or when calling sync
rule bufferStoredConvergesOnMidpoint(env e, method f)
filtered {
    f ->
        f.selector == sig:sync().selector ||
        f.selector == sig:setRateLimitPerSecond(uint128).selector
} {
    uint256 bufferStoredPre = bufferStored();
    uint256 bufferPre = buffer(e);

    require uint32Max() >= e.block.timestamp; /// only allow timestamps less than or equal to 2^32 - 1
    require to_mathint(lastBufferUsedTime()) < to_mathint(e.block.timestamp);
    require rateLimitPerSecond() != 0; /// ensure rate limit is non zero so that buffer changes
    require bufferPre != midPoint();


    requireInvariant midPointHalfBufferCap(); /// ensure sane midpoint
    requireInvariant bufferLteUint112(e);
    requireInvariant bufferCapLteUint112();

    calldataarg args;

    /// possible function calls:
    ///  - deplete buffer
    ///  - replenish buffer --- if already at bufferCap, no state changes
    ///  - setBufferCap
    ///  - setRateLimitPerSecond
    f(e, args);

    uint256 bufferStoredPost = bufferStored();

    assert absDelta(bufferStoredPre, midPoint()) > absDelta(bufferStoredPost, midPoint()), "buffer stored not converging on midpoint";
}

/// only depletes or replenishes atomically when depleting or replenishing buffer
rule bufferUpdatesDeplete(env e, uint256 amount) {
    mathint bufferPre = to_mathint(buffer(e));

    requireInvariant midPointHalfBufferCap(); /// ensure sane midpoint
    requireInvariant bufferLteUint112(e);
    requireInvariant bufferCapLteUint112();

    calldataarg args;

    depleteBuffer(e, amount);

    mathint bufferPost = to_mathint(buffer(e));

    assert (bufferPre - amount) == bufferPost, "buffer not decreased on replenish";
}

/// only depletes or replenishes atomically when depleting or replenishing buffer
rule bufferUpdatesReplenish(env e, uint256 amount) {
    mathint bufferPre = to_mathint(buffer(e));

    requireInvariant midPointHalfBufferCap(); /// ensure sane midpoint
    requireInvariant bufferLteUint112(e);
    requireInvariant bufferCapLteUint112();

    calldataarg args;

    replenishBuffer(e, amount);

    mathint bufferPost = to_mathint(buffer(e));

    assert (bufferPre + amount) == bufferPost, "buffer not increased on replenish";
}
