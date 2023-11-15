pragma solidity =0.8.19;

import {Math} from "@src/util/Math.sol";

import "@forge-std/Test.sol";

import {RateLimited} from "@src/impl/RateLimited.sol";
import {MockRateLimited} from "@zelt-test/mock/MockRateLimited.sol";

contract UnitTestRateLimited is Test {
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
    MockRateLimited rlm;

    /// @notice maximum rate limit per second in RateLimitedV2
    uint256 private constant maxRateLimitPerSecond = 1_000_000e18;

    /// @notice rate limit per second in RateLimitedV2
    uint128 private constant rateLimitPerSecond = 10_000e18;

    /// @notice buffer cap in RateLimitedV2
    uint128 private constant bufferCap = 10_000_000e18;

    function setUp() public {
        rlm = new MockRateLimited(
            maxRateLimitPerSecond,
            rateLimitPerSecond,
            bufferCap
        );
    }

    function testSetup() public {
        assertEq(rlm.bufferCap(), bufferCap);
        assertEq(rlm.rateLimitPerSecond(), rateLimitPerSecond);
        assertEq(rlm.MAX_RATE_LIMIT_PER_SECOND(), maxRateLimitPerSecond);
        assertEq(rlm.buffer(), bufferCap); /// buffer has not been depleted
    }

    function testDepleteBuffer(uint128 amountToPull, uint16 warpAmount) public {
        if (amountToPull > bufferCap) {
            vm.expectRevert("RateLimited: rate limit hit");
            rlm.depleteBuffer(amountToPull);
        } else {
            vm.expectEmit(true, false, false, true, address(rlm));
            emit BufferUsed(amountToPull, bufferCap - amountToPull);
            rlm.depleteBuffer(amountToPull);
            uint256 endingBuffer = rlm.buffer();
            assertEq(endingBuffer, bufferCap - amountToPull);
            assertEq(block.timestamp, rlm.lastBufferUsedTime());

            vm.warp(block.timestamp + warpAmount);

            uint256 accruedBuffer = warpAmount * rateLimitPerSecond;
            uint256 expectedBuffer = Math.min(
                endingBuffer + accruedBuffer,
                bufferCap
            );
            assertEq(expectedBuffer, rlm.buffer());
        }
    }

    function testReplenishBuffer(
        uint128 amountToReplenish,
        uint16 warpAmount
    ) public {
        rlm.depleteBuffer(bufferCap); /// fully exhaust buffer
        assertEq(rlm.buffer(), 0);

        uint256 actualAmountToReplenish = Math.min(
            amountToReplenish,
            bufferCap
        );
        vm.expectEmit(true, false, false, true, address(rlm));
        emit BufferReplenished(amountToReplenish, actualAmountToReplenish);

        rlm.replenishBuffer(amountToReplenish);
        assertEq(rlm.buffer(), actualAmountToReplenish);
        assertEq(block.timestamp, rlm.lastBufferUsedTime());

        vm.warp(block.timestamp + warpAmount);

        uint256 accruedBuffer = warpAmount * rateLimitPerSecond;
        uint256 expectedBuffer = Math.min(
            amountToReplenish + accruedBuffer,
            bufferCap
        );
        assertEq(expectedBuffer, rlm.buffer());
    }

    function testDepleteThenReplenishBuffer(
        uint128 amountToDeplete,
        uint128 amountToReplenish,
        uint16 warpAmount
    ) public {
        uint256 actualAmountToDeplete = Math.min(amountToDeplete, bufferCap);
        rlm.depleteBuffer(actualAmountToDeplete); /// deplete buffer
        assertEq(rlm.buffer(), bufferCap - actualAmountToDeplete);

        uint256 actualAmountToReplenish = Math.min(
            amountToReplenish,
            bufferCap
        );

        rlm.replenishBuffer(amountToReplenish);
        uint256 finalState = bufferCap -
            actualAmountToDeplete +
            actualAmountToReplenish;
        uint256 endingBuffer = Math.min(finalState, bufferCap);
        assertEq(rlm.buffer(), endingBuffer);
        assertEq(block.timestamp, rlm.lastBufferUsedTime());

        vm.warp(block.timestamp + warpAmount);

        uint256 accruedBuffer = warpAmount * rateLimitPerSecond;
        uint256 expectedBuffer = Math.min(
            finalState + accruedBuffer,
            bufferCap
        );
        assertEq(expectedBuffer, rlm.buffer());
    }

    function testReplenishWhenAtBufferCapHasNoEffect(
        uint128 amountToReplenish
    ) public {
        rlm.replenishBuffer(amountToReplenish);
        assertEq(rlm.buffer(), bufferCap);
        assertEq(block.timestamp, rlm.lastBufferUsedTime());
    }
}
