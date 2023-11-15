pragma solidity =0.8.19;

import {Math} from "@src/util/Math.sol";

import "@forge-std/Test.sol";

import {RateLimited} from "@src/impl/RateLimited.sol";
import {MockRateLimitedMidpoint} from "@zelt-test/mock/MockRateLimitedMidpoint.sol";

contract UnitTestRateLimitedMidpoint is Test {
    /// @notice event emitted when buffer cap is updated
    event BufferCapUpdate(uint256 oldBufferCap, uint256 newBufferCap);

    /// @notice event emitted when rate limit per second is updated
    event RateLimitPerSecondUpdate(
        uint256 oldRateLimitPerSecond,
        uint256 newRateLimitPerSecond
    );

    /// @notice event emitted when buffer gets eaten into
    event BufferUsed(uint256 amountUsed, uint256 bufferRemaining);

    /// @notice event emitted when buffer gets replenished
    event BufferReplenished(uint256 amountReplenished, uint256 bufferRemaining);

    /// @notice rate limited v2 contract
    MockRateLimitedMidpoint rlm;

    /// @notice maximum rate limit per second in RateLimitedV2
    uint256 private constant maxRateLimitPerSecond = 1_000_000e18;

    /// @notice rate limit per second in RateLimitedV2
    uint128 private constant rateLimitPerSecond = 10_000e18;

    /// @notice buffer cap in RateLimitedV2
    uint112 private constant bufferCap = 10_000_000e18;

    function setUp() public {
        rlm = new MockRateLimitedMidpoint(
            maxRateLimitPerSecond,
            rateLimitPerSecond,
            bufferCap
        );
    }

    function testSetup() public {
        assertEq(rlm.bufferCap(), bufferCap);
        assertEq(rlm.rateLimitPerSecond(), rateLimitPerSecond);
        assertEq(rlm.MAX_RATE_LIMIT_PER_SECOND(), maxRateLimitPerSecond);

        /// buffer cap starts off at midpoint
        assertEq(rlm.buffer(), bufferCap / 2); /// buffer has not been depleted
        assertEq(
            rlm.midPoint(),
            bufferCap / 2,
            "midpoint should be half of bufferCap"
        );
    }

    function testDepleteBuffer(uint128 amountToPull, uint16 warpAmount) public {
        if (amountToPull > rlm.midPoint()) {
            vm.expectRevert("RateLimited: rate limit hit");
            rlm.depleteBuffer(amountToPull);
        } else {
            uint256 startingBuffer = rlm.buffer();
            vm.expectEmit(true, false, false, true, address(rlm));
            emit BufferUsed(amountToPull, startingBuffer - amountToPull);
            rlm.depleteBuffer(amountToPull);

            uint256 endingBuffer = rlm.buffer();

            assertEq(
                endingBuffer,
                rlm.midPoint() - amountToPull,
                "incorrect ending buffer"
            );
            assertEq(
                block.timestamp,
                rlm.lastBufferUsedTime(),
                "incorrect time after depleting buffer"
            );

            vm.warp(block.timestamp + warpAmount);

            uint256 accruedBuffer = warpAmount * rateLimitPerSecond;
            uint256 expectedBuffer = Math.min(
                endingBuffer + accruedBuffer,
                rlm.midPoint()
            );
            assertEq(
                expectedBuffer,
                rlm.buffer(),
                "incorrect buffer after warp"
            );
        }
    }

    function testReplenishBuffer(
        uint128 amountToReplenish,
        uint16 warpAmount
    ) public {
        rlm.depleteBuffer(rlm.buffer()); /// fully exhaust buffer
        assertEq(rlm.buffer(), 0, "buffer should be empty");

        amountToReplenish = uint128(
            _bound(amountToReplenish, 1, rlm.bufferCap() - rlm.buffer())
        ); /// can only replenish up to remaining buffer left

        vm.expectEmit(true, false, false, true, address(rlm));
        emit BufferReplenished(amountToReplenish, amountToReplenish);

        rlm.replenishBuffer(amountToReplenish);
        assertEq(
            rlm.buffer(),
            amountToReplenish,
            "incorrect buffer after replenishing"
        );
        assertEq(
            block.timestamp,
            rlm.lastBufferUsedTime(),
            "incorrect time after replenishing"
        );

        uint256 startingBufferBeforeWarp = rlm.buffer();

        vm.warp(block.timestamp + uint256(warpAmount));

        uint256 accruedBuffer = warpAmount * rateLimitPerSecond;
        uint256 expectedBuffer = rlm.midPoint(); /// start off at midpoint, so if no assignment, we are at correct point
        uint256 midPoint = rlm.midPoint();

        //// depletion

        //// t0 | ---------------- | ----------------- |
        ////                       ^

        //// t0 | ---------------- | ----------------- |
        ////    ^

        /// scenario A

        //// replenish
        //// t0 | ---------------- | ----------------- |
        ////               ^

        //// t1 | ---------------- | ----------------- |
        ////                    ^

        /// scenario B

        //// replenish
        //// t0 | ---------------- | ----------------- |
        ////                                ^

        //// t1 | ---------------- | ----------------- |
        ////                         ^

        /// scenario C

        //// replenish
        //// t0 | ---------------- | ----------------- |
        ////                                ^

        //// t1 | ---------------- | ----------------- |
        ////                    ^ X -- gets set to midpoint

        //// B
        //// t0 = startingBufferBeforeWarp
        //// if started at greater than midpoint, then subtract accrued buffer
        if (startingBufferBeforeWarp > midPoint) {
            if (
                startingBufferBeforeWarp >= accruedBuffer &&
                startingBufferBeforeWarp - accruedBuffer > midPoint /// handle scenario C
            ) {
                expectedBuffer = startingBufferBeforeWarp - accruedBuffer;
            }
            //// A
        } else if (startingBufferBeforeWarp < midPoint) {
            expectedBuffer = startingBufferBeforeWarp + accruedBuffer > midPoint
                ? midPoint
                : startingBufferBeforeWarp + accruedBuffer;
        }

        assertEq(expectedBuffer, rlm.buffer(), "incorrect buffer at end time");
    }

    function testDepleteThenReplenishBuffer(
        uint128 amountToDeplete,
        uint128 amountToReplenish,
        uint16 warpAmount
    ) public {
        amountToDeplete = uint128(_bound(amountToDeplete, 0, rlm.buffer())); /// can only deplete full buffer
        amountToReplenish = uint128(
            _bound(amountToReplenish, 0, rlm.buffer() - amountToDeplete)
        ); /// can only replenish up to bufferCap
        rlm.depleteBuffer(amountToDeplete); /// deplete buffer
        assertEq(
            rlm.buffer(),
            rlm.midPoint() - amountToDeplete,
            "incorrect buffer after depletion"
        );

        rlm.replenishBuffer(amountToReplenish);

        assertEq(
            rlm.buffer(),
            rlm.midPoint() - amountToDeplete + amountToReplenish,
            "incorrect buffer after deplete and replenish"
        );
        assertEq(
            block.timestamp,
            rlm.lastBufferUsedTime(),
            "last buffer used time incorrect"
        );

        uint256 startingBufferBeforeWarp = rlm.buffer();

        vm.warp(block.timestamp + uint256(warpAmount));

        uint256 accruedBuffer = warpAmount * rateLimitPerSecond;
        uint256 expectedBuffer = rlm.midPoint(); /// start off at midpoint, so if no assignment, we are at correct point
        uint256 midPoint = rlm.midPoint();

        if (startingBufferBeforeWarp > midPoint) {
            if (
                startingBufferBeforeWarp >= accruedBuffer &&
                startingBufferBeforeWarp - accruedBuffer > midPoint /// handle scenario C
            ) {
                expectedBuffer = startingBufferBeforeWarp - accruedBuffer;
            }
            //// A
        } else if (startingBufferBeforeWarp < midPoint) {
            expectedBuffer = startingBufferBeforeWarp + accruedBuffer > midPoint
                ? midPoint
                : startingBufferBeforeWarp + accruedBuffer;
        }

        assertEq(expectedBuffer, rlm.buffer(), "incorrect buffer at end time");
    }

    function testReplenish(uint128 amountToReplenish) public {
        amountToReplenish = uint128(
            _bound(amountToReplenish, 0, rlm.bufferCap() / 2)
        );
        rlm.replenishBuffer(amountToReplenish);
        assertEq(
            rlm.buffer(),
            rlm.midPoint() + amountToReplenish,
            "incorrect buffer after replenishing"
        );
        assertEq(
            block.timestamp,
            rlm.lastBufferUsedTime(),
            "incorrect timestamp after replenishing"
        );
    }

    function testReplenishOverBufferCapFails() public {
        uint256 amountToReplenish = rlm.bufferCap() + 1;
        vm.expectRevert("RateLimited: buffer cap overflow");
        rlm.replenishBuffer(amountToReplenish);
    }

    function testDepleteMoreThanBufferFails() public {
        uint256 depleteAmount = rlm.buffer() + 1;
        vm.expectRevert("RateLimited: rate limit hit");
        rlm.depleteBuffer(depleteAmount);
    }

    function testCanUpdateRateLimitPerSecond() public {
        uint128 newRateLimitPerSecond = 100e18;

        rlm.setRateLimitPerSecond(newRateLimitPerSecond);

        assertEq(
            rlm.rateLimitPerSecond(),
            newRateLimitPerSecond,
            "incorrect rate limit per second"
        );
    }

    function testCanUpdateBufferCap() public {
        uint112 newBuffer = 100e18;

        rlm.setBufferCap(newBuffer); /// in this scenario, buffer is full, so only depletes are possible

        assertEq(rlm.bufferCap(), newBuffer, "incorrect buffer cap");
        assertEq(rlm.midPoint(), newBuffer / 2, "incorrect midpoint");
        assertEq(rlm.bufferStored(), newBuffer, "incorrect buffer stored");
    }

    function testCanSync() public {
        rlm.sync();

        assertEq(rlm.bufferCap(), bufferCap, "incorrect buffer cap");
        assertEq(rlm.midPoint(), bufferCap / 2, "incorrect midpoint");
        assertEq(rlm.bufferStored(), bufferCap / 2, "incorrect buffer stored");
    }
}
