pragma solidity =0.8.19;

import {Math} from "@zelt-src/util/Math.sol";

/// @notice two rate storage slots per rate limit
struct RateLimit {
    /// @notice the rate per second for this contract
    uint128 rateLimitPerSecond;
    /// @notice the cap of the buffer that can be used at once
    uint128 bufferCap;
    /// @notice the last time the buffer was used by the contract
    uint32 lastBufferUsedTime;
    /// @notice the buffer at the timestamp of lastBufferUsedTime
    uint224 bufferStored;
}

/// @title abstract contract for putting a rate limit on how fast a contract
/// can perform an action e.g. Minting
/// @author Elliot Friedman
library RateLimitCommonLibrary {
    /// @notice event emitted when buffer cap is updated
    event BufferCapUpdate(uint256 oldBufferCap, uint256 newBufferCap);

    /// @notice event emitted when rate limit per second is updated
    event RateLimitPerSecondUpdate(
        uint256 oldRateLimitPerSecond,
        uint256 newRateLimitPerSecond
    );

    /// @notice the amount of action used before hitting limit
    /// @dev replenishes at rateLimitPerSecond per second up to bufferCap
    /// @param limit pointer to the rate limit object
    function buffer(RateLimit storage limit) public view returns (uint256) {
        uint256 elapsed;
        unchecked {
            /// if block.timestamp > uint32 max this will still work as bits gt 32 will be truncated
            elapsed = uint32(block.timestamp) - limit.lastBufferUsedTime;
        }

        return
            Math.min(
                limit.bufferStored + (limit.rateLimitPerSecond * elapsed),
                limit.bufferCap
            );
    }

    /// @notice syncs the buffer to the current time
    /// @dev should be called before any action that
    /// updates buffer cap or rate limit per second
    /// @param limit pointer to the rate limit object
    function sync(RateLimit storage limit) internal {
        uint224 newBuffer = uint224(buffer(limit));
        uint32 blockTimestamp = uint32(block.timestamp);

        limit.lastBufferUsedTime = blockTimestamp;
        limit.bufferStored = newBuffer;
    }

    /// @notice set the rate limit per second
    /// @param limit pointer to the rate limit object
    /// @param newRateLimitPerSecond the new rate limit per second
    function setRateLimitPerSecond(
        RateLimit storage limit,
        uint128 newRateLimitPerSecond
    ) internal {
        sync(limit);
        uint256 oldRateLimitPerSecond = limit.rateLimitPerSecond;
        limit.rateLimitPerSecond = newRateLimitPerSecond;

        emit RateLimitPerSecondUpdate(
            oldRateLimitPerSecond,
            newRateLimitPerSecond
        );
    }

    /// @notice set the buffer cap, but first sync to accrue all rate limits accrued
    /// @param limit pointer to the rate limit object
    /// @param newBufferCap the new buffer cap to set
    function setBufferCap(
        RateLimit storage limit,
        uint128 newBufferCap
    ) internal {
        sync(limit);

        uint256 oldBufferCap = limit.bufferCap;
        limit.bufferCap = newBufferCap;

        emit BufferCapUpdate(oldBufferCap, newBufferCap);
    }
}
