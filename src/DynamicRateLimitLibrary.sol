pragma solidity =0.8.19;

import {Math} from "@src/Math.sol";
import {RateLimit, RateLimitCommonLibrary} from "@src/RateLimitCommonLibrary.sol";

/// @title abstract contract for putting a rate limit on how fast a contract
/// can perform an action e.g. Minting
/// @author Elliot Friedman
library DynamicRateLimitLibrary {
    /// @notice dynamic rate limit 
    using RateLimitCommonLibrary for RateLimit;

    /// @notice event emitted when buffer gets eaten into
    event BufferUsed(uint256 amountUsed, uint256 bufferRemaining);

    /// @notice event emitted when buffer gets replenished
    event BufferReplenished(uint256 amountReplenished, uint256 bufferRemaining);

    /// @notice the method that enforces the rate limit.
    /// Decreases buffer by "amount".
    /// If buffer is <= amount, revert
    /// @param limit pointer to the rate limit object
    /// @param amount to decrease buffer by
    /// @param prevTvlAmount the previous tvl amount before the action
    function depleteBuffer(
        RateLimit storage limit,
        uint256 amount,
        uint256 prevTvlAmount
    ) internal {
        uint256 newBuffer = limit.buffer();

        require(newBuffer != 0, "RateLimited: no rate limit buffer");
        require(amount <= newBuffer, "RateLimited: rate limit hit");

        uint32 blockTimestamp = uint32(block.timestamp);
        uint224 newBufferStored = uint224(newBuffer - amount);

        /// gas optimization to only use a single SSTORE
        limit.lastBufferUsedTime = blockTimestamp;
        limit.bufferStored = newBufferStored;

        /// decrease both buffer cap and rate limit per second proportionally to new TVL
        uint256 newTvl = prevTvlAmount - amount;
        uint128 newRateLimitPerSecond = uint128(
            (limit.rateLimitPerSecond * newTvl) / prevTvlAmount
        );
        uint128 newBufferCap = uint128(
            (limit.bufferCap * newTvl) / prevTvlAmount
        );

        limit.rateLimitPerSecond = newRateLimitPerSecond;
        limit.bufferCap = newBufferCap;

        emit BufferUsed(amount, newBufferStored);
    }

    /// @notice function to replenish buffer, and increase rate limit per second and buffer cap
    /// @param limit pointer to the rate limit object
    /// @param amount to increase buffer by if under buffer cap
    /// @param prevTvlAmount the previous tvl amount before the action
    function replenishBuffer(
        RateLimit storage limit,
        uint256 amount,
        uint256 prevTvlAmount
    ) internal {
        uint256 newBuffer = limit.buffer();

        uint256 _bufferCap = limit.bufferCap; /// gas opti, save an SLOAD

        /// cannot replenish any further if already at buffer cap
        if (newBuffer == _bufferCap) {
            /// save an SSTORE + some stack operations if buffer cannot be increased.
            /// last buffer used time doesn't need to be updated as buffer cannot
            /// increase past the buffer cap
            return;
        }

        uint32 blockTimestamp = uint32(block.timestamp); /// truncate bits over uint32

        /// ensure that bufferStored cannot be gt buffer cap
        uint224 newBufferStored = uint224(Math.min(newBuffer + amount, _bufferCap));

        /// gas optimization to only use a single SSTORE
        limit.lastBufferUsedTime = blockTimestamp;
        limit.bufferStored = newBufferStored;

        /// increase both buffer cap and rate limit per second proportionally to new TVL
        uint256 newTvl = prevTvlAmount + amount;
        uint128 newRateLimitPerSecond = uint128(
            (limit.rateLimitPerSecond * newTvl) / prevTvlAmount
        );
        uint128 newBufferCap = uint128((_bufferCap * newTvl) / prevTvlAmount);

        limit.rateLimitPerSecond = newRateLimitPerSecond;
        limit.bufferCap = newBufferCap;

        emit BufferReplenished(amount, newBufferStored);
    }
}
