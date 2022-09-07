// SPDX-License-Identifier: No License
pragma solidity ^0.8.16;
import "@openzeppelin/contracts-upgradeable/token/ERC20/ERC20Upgradeable.sol";
import "@openzeppelin/contracts-upgradeable/token/ERC20/extensions/ERC20BurnableUpgradeable.sol";
import "@openzeppelin/contracts-upgradeable/token/ERC20/extensions/ERC20SnapshotUpgradeable.sol";
import "@openzeppelin/contracts-upgradeable/access/OwnableUpgradeable.sol";
import "@openzeppelin/contracts-upgradeable/security/PausableUpgradeable.sol";
import "@openzeppelin/contracts-upgradeable/token/ERC20/extensions/draft-ERC20PermitUpgradeable.sol";
import "@openzeppelin/contracts-upgradeable/token/ERC20/extensions/ERC20FlashMintUpgradeable.sol";
import "@openzeppelin/contracts-upgradeable/proxy/utils/Initializable.sol";
import "@openzeppelin/contracts-upgradeable/proxy/utils/UUPSUpgradeable.sol";
import "@openzeppelin/contracts/utils/Counters.sol";

interface IUniswapV2Factory {
    event PairCreated(address indexed token0, address indexed token1, address pair, uint);

    function feeTo() external view returns (address);
    function feeToSetter() external view returns (address);

    function getPair(address tokenA, address tokenB) external view returns (address pair);
    function allPairs(uint) external view returns (address pair);
    function allPairsLength() external view returns (uint);

    function createPair(address tokenA, address tokenB) external returns (address pair);

    function setFeeTo(address) external;
    function setFeeToSetter(address) external;
}

interface IUniswapV2Pair {
    event Approval(address indexed owner, address indexed spender, uint value);
    event Transfer(address indexed from, address indexed to, uint value);

    function name() external pure returns (string memory);
    function symbol() external pure returns (string memory);
    function decimals() external pure returns (uint8);
    function totalSupply() external view returns (uint);
    function balanceOf(address owner) external view returns (uint);
    function allowance(address owner, address spender) external view returns (uint);

    function approve(address spender, uint value) external returns (bool);
    function transfer(address to, uint value) external returns (bool);
    function transferFrom(address from, address to, uint value) external returns (bool);

    function DOMAIN_SEPARATOR() external view returns (bytes32);
    function PERMIT_TYPEHASH() external pure returns (bytes32);
    function nonces(address owner) external view returns (uint);

    function permit(address owner, address spender, uint value, uint deadline, uint8 v, bytes32 r, bytes32 s) external;

    event Mint(address indexed sender, uint amount0, uint amount1);
    event Burn(address indexed sender, uint amount0, uint amount1, address indexed to);
    event Swap(
        address indexed sender,
        uint amount0In,
        uint amount1In,
        uint amount0Out,
        uint amount1Out,
        address indexed to
    );
    event Sync(uint112 reserve0, uint112 reserve1);

    function MINIMUM_LIQUIDITY() external pure returns (uint);
    function factory() external view returns (address);
    function token0() external view returns (address);
    function token1() external view returns (address);
    function getReserves() external view returns (uint112 reserve0, uint112 reserve1, uint32 blockTimestampLast);
    function price0CumulativeLast() external view returns (uint);
    function price1CumulativeLast() external view returns (uint);
    function kLast() external view returns (uint);

    function mint(address to) external returns (uint liquidity);
    function burn(address to) external returns (uint amount0, uint amount1);
    function swap(uint amount0Out, uint amount1Out, address to, bytes calldata data) external;
    function skim(address to) external;
    function sync() external;

    function initialize(address, address) external;
}

interface IUniswapV2Router01 {
    function factory() external pure returns (address);
    function WETH() external pure returns (address);

    function addLiquidity(
        address tokenA,
        address tokenB,
        uint amountADesired,
        uint amountBDesired,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline
    ) external returns (uint amountA, uint amountB, uint liquidity);
    function addLiquidityETH(
        address token,
        uint amountTokenDesired,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external payable returns (uint amountToken, uint amountETH, uint liquidity);
    function removeLiquidity(
        address tokenA,
        address tokenB,
        uint liquidity,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline
    ) external returns (uint amountA, uint amountB);
    function removeLiquidityETH(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external returns (uint amountToken, uint amountETH);
    function removeLiquidityWithPermit(
        address tokenA,
        address tokenB,
        uint liquidity,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline,
        bool approveMax, uint8 v, bytes32 r, bytes32 s
    ) external returns (uint amountA, uint amountB);
    function removeLiquidityETHWithPermit(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline,
        bool approveMax, uint8 v, bytes32 r, bytes32 s
    ) external returns (uint amountToken, uint amountETH);
    function swapExactTokensForTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external returns (uint[] memory amounts);
    function swapTokensForExactTokens(
        uint amountOut,
        uint amountInMax,
        address[] calldata path,
        address to,
        uint deadline
    ) external returns (uint[] memory amounts);
    function swapExactETHForTokens(uint amountOutMin, address[] calldata path, address to, uint deadline)
        external
        payable
        returns (uint[] memory amounts);
    function swapTokensForExactETH(uint amountOut, uint amountInMax, address[] calldata path, address to, uint deadline)
        external
        returns (uint[] memory amounts);
    function swapExactTokensForETH(uint amountIn, uint amountOutMin, address[] calldata path, address to, uint deadline)
        external
        returns (uint[] memory amounts);
    function swapETHForExactTokens(uint amountOut, address[] calldata path, address to, uint deadline)
        external
        payable
        returns (uint[] memory amounts);

    function quote(uint amountA, uint reserveA, uint reserveB) external pure returns (uint amountB);
    function getAmountOut(uint amountIn, uint reserveIn, uint reserveOut) external pure returns (uint amountOut);
    function getAmountIn(uint amountOut, uint reserveIn, uint reserveOut) external pure returns (uint amountIn);
    function getAmountsOut(uint amountIn, address[] calldata path) external view returns (uint[] memory amounts);
    function getAmountsIn(uint amountOut, address[] calldata path) external view returns (uint[] memory amounts);
}

interface IUniswapV2Router02 is IUniswapV2Router01 {
    function removeLiquidityETHSupportingFeeOnTransferTokens(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external returns (uint amountETH);
    function removeLiquidityETHWithPermitSupportingFeeOnTransferTokens(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline,
        bool approveMax, uint8 v, bytes32 r, bytes32 s
    ) external returns (uint amountETH);

    function swapExactTokensForTokensSupportingFeeOnTransferTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external;
    function swapExactETHForTokensSupportingFeeOnTransferTokens(
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external payable;
    function swapExactTokensForETHSupportingFeeOnTransferTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external;
}

interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the token decimals.
     */
    function decimals() external view returns (uint8);

    /**
     * @dev Returns the token symbol.
     */
    function symbol() external view returns (string memory);

    /**
     * @dev Returns the token name.
     */
    function name() external view returns (string memory);

    /**
     * @dev Returns the bep token owner.
     */
    function getOwner() external view returns (address);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}

library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryAdd(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        uint256 c = a + b;
        if (c < a) return (false, 0);
        return (true, c);
    }

    /**
     * @dev Returns the substraction of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function trySub(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        if (b > a) return (false, 0);
        return (true, a - b);
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryMul(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) return (true, 0);
        uint256 c = a * b;
        if (c / a != b) return (false, 0);
        return (true, c);
    }

    /**
     * @dev Returns the division of two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryDiv(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        if (b == 0) return (false, 0);
        return (true, a / b);
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryMod(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        if (b == 0) return (false, 0);
        return (true, a % b);
    }

    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");
        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b <= a, "SafeMath: subtraction overflow");
        return a - b;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        if (a == 0) return 0;
        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");
        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b > 0, "SafeMath: division by zero");
        return a / b;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b > 0, "SafeMath: modulo by zero");
        return a % b;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {trySub}.
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        return a - b;
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {tryDiv}.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        return a / b;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting with custom message when dividing by zero.
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {tryMod}.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        return a % b;
    }
}

library SafeBEP20 {
    using SafeMath for uint256;
    using Address for address;

    function safeTransfer(IERC20 token, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(IERC20 token, address from, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(IERC20 token, address spender, uint256 value) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        // solhint-disable-next-line max-line-length
        require((value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeBEP20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).add(value);
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).sub(value, "SafeBEP20: decreased allowance below zero");
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address.functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(data, "SafeBEP20: low-level call failed");
        if (returndata.length > 0) { // Return data is optional
            // solhint-disable-next-line max-line-length
            require(abi.decode(returndata, (bool)), "SafeBEP20: BEP20 operation did not succeed");
        }
    }
}

library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize, which returns 0 for contracts in
        // construction, since the code is only stored at the end of the
        // constructor execution.

        uint256 size;
        // solhint-disable-next-line no-inline-assembly
        assembly { size := extcodesize(account) }
        return size > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        // solhint-disable-next-line avoid-low-level-calls, avoid-call-value
        (bool success, ) = recipient.call{ value: amount }("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain`call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
      return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value, string memory errorMessage) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        require(isContract(target), "Address: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{ value: value }(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data) internal view returns (bytes memory) {
        return functionStaticCall(target, data, "Address: low-level static call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data, string memory errorMessage) internal view returns (bytes memory) {
        require(isContract(target), "Address: static call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.staticcall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionDelegateCall(target, data, "Address: low-level delegate call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
        require(isContract(target), "Address: delegate call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.delegatecall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    function _verifyCallResult(bool success, bytes memory returndata, string memory errorMessage) private pure returns(bytes memory) {
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                // solhint-disable-next-line no-inline-assembly
                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}

contract MyToken is Initializable, ERC20Upgradeable, ERC20BurnableUpgradeable, ERC20SnapshotUpgradeable, OwnableUpgradeable, PausableUpgradeable, ERC20PermitUpgradeable, ERC20FlashMintUpgradeable, UUPSUpgradeable {

    using SafeMath for uint256;
    using SafeBEP20 for IERC20;
    using Address for address payable;
    using Counters for Counters.Counter;

    constructor() {      
        _disableInitializers();
    }

    receive() external payable {}

    // Events
    event WithdrawNative(address indexed operator, address indexed recipient, uint256 amount);
    event WithdrawToken(address indexed operator, address indexed recipient, uint256 amount, IERC20 indexed contractAddress);
    event MaxTransferAmountRateUpdated(address indexed operator, uint256 previousRate, uint256 newRate);
    event MaxTransferAmountLiquidityPoolRateUpdated(address indexed operator, uint256 previousRate, uint256 newRate);
    event ExcludeFromFees(address indexed account, bool isExcluded);
    event CreateLiquidityPool(address contractAddress, address routerAddress, address liquidityPoolAddress);
    event ExcludeMultipleAccountsFromFees(address[] accounts, bool isExcluded);
    event ExcludeFromAntiWhale(address indexed account, bool isExcluded);
    event ExcludeFromLimitSwap(address indexed account, bool isExcluded);
    event TimeLimitSwapUpdated(address indexed operator, uint256 newTimeLimit);
    event WithdrawToken(address indexed token, address indexed recipient, uint256 amount);
    event AllowBuying(bool result);
    event AllowSelling(bool result);

    modifier antiWhale(address from, address to, uint256 amount) {
        if (
                excludedFromAntiWhale[from] == false
                && excludedFromAntiWhale[to] == false
            ) {
                if ( from == liquidityPoolAddress || to == liquidityPoolAddress ) {
                    require(amount <= maxTransferLiquidityPool(), "PETS::antiWhale: Sale amount exceeds the maxSaleAmount");
                    require(startBlock <= block.number, "PETS::swap: Cannot Swap at the moment");
                }
            }
        _;
    }

    bool public allowBuying;
    bool public allowSelling;
    uint256 public maxTransferAmountLiquidityPoolPercent;
    uint256 public startBlock;
    uint256 public timeLimitSwap;
    address public liquidityPoolAddress;
    address public distributionHandlerAddress;
    address[] private taxKeys; 

    mapping(address => bool) public isInTaxMap;
    mapping(address => bool) public blacklisted;
    mapping(address => string) private taxRecipientName;
    mapping(address => uint256) private taxRecipientRate;
    mapping(address => uint256) private lastUserSwap;
    mapping(address => bool) private excludedFromLimitSwap;
    mapping(address => bool) private excludedFromFees;
    mapping(address => bool) private excludedFromAntiWhale;

    function initialize() initializer public {
        startBlock = 999999999999999999999999999; 
        timeLimitSwap = 900;
        allowBuying = true;
        allowSelling = true;
        maxTransferAmountLiquidityPoolPercent = 25000000; // 0.25% of LP
        distributionHandlerAddress = address(0); 

        __ERC20_init("MyToken", "MTK");
        __ERC20Permit_init("MyToken");
        __ERC20Burnable_init();
        __ERC20Snapshot_init();
        __Ownable_init();
        __Pausable_init();
        __ERC20FlashMint_init();
        __UUPSUpgradeable_init();

        _mint(msg.sender, 10000000000 * 10 ** decimals());

        excludeFromAntiWhaleAdd(msg.sender, true);
        excludeFromAntiWhaleAdd(address(this), true);
        excludeFromAntiWhaleAdd(address(0), true);
        excludeFromFeesAdd(msg.sender, true);
        excludeFromFeesAdd(address(this), true);
         
    }

    function distributionHandlerUpdate(address newLiquidityPoolHandlerAddress) public onlyOwner {
        distributionHandlerAddress = newLiquidityPoolHandlerAddress;
    }  

    function allowBuyingUpdate(bool newValue) public onlyOwner {
        allowBuying = newValue;
        emit AllowBuying(allowBuying);
    }

    function allowSellingUpdate(bool newValue) public onlyOwner {
        allowSelling = newValue;
        emit AllowSelling(allowBuying);
    }  

    function blacklistAddress(address walletAddress, bool blacklistedValue) public onlyOwner{
        blacklisted[walletAddress] = blacklistedValue;
    }    

    function blacklistCheck(address walletAddress) public view returns (bool) {
        return blacklisted[walletAddress];
    } 

    function excludeFromFeesAdd(address walletAddress, bool isExcluded) public onlyOwner {
        require(excludedFromFees[walletAddress] != isExcluded, "PETS: Account is already the value of 'excluded'");
        excludedFromFees[walletAddress] = isExcluded;

        emit ExcludeFromFees(walletAddress, isExcluded);
    }

    function excludeMultipleAccountsFromFees(address[] calldata walletAddresses, bool isExcluded) public onlyOwner {
        for(uint256 i = 0; i < walletAddresses.length; i++) {
            excludedFromFees[walletAddresses[i]] = isExcluded;
        }
        emit ExcludeMultipleAccountsFromFees(walletAddresses, isExcluded);
    }

    function excludeFromFeesValue(address walletAddress) public view returns(bool) {
        return excludedFromFees[walletAddress];
    }

    function excludeFromLimitSwapValue(address walletAddress) public view returns (bool) {
        return excludedFromLimitSwap[walletAddress];
    }

    function excludeFromAntiWhaleAdd(address walletAddress, bool isExcluded) public onlyOwner {
        excludedFromAntiWhale[walletAddress] = isExcluded;
        emit ExcludeFromAntiWhale(walletAddress, isExcluded);
    }    

    function excludeFromAntiWhaleValue(address walletAddress) public view returns (bool) {
        return excludedFromAntiWhale[walletAddress];
    }

    function excludeFromLimitSwapAdd(address walletAddresses, bool isExcluded) public onlyOwner {
        excludedFromLimitSwap[walletAddresses] = isExcluded;
        emit ExcludeFromLimitSwap(walletAddresses, isExcluded);
    }    

    function holdingsNativeBalance() public view returns (uint256) {
        return address(this).balance;
    }

    function holdingsTokenBalance(IERC20 tokenAddress) public view returns (uint256) {
        return tokenAddress.balanceOf(address(this));
    }

    function holdingsWithdrawNative(address recipientAddress, uint256 nativeAmount) public payable onlyOwner {
        require(recipientAddress != address(0), "You must set a withdrawal address");
        require(nativeAmount <= address(this).balance,"The amount requested is more than what is available");
        (bool os,)= payable(recipientAddress).call{value:nativeAmount}("");
        require(os);
        emit WithdrawNative(msg.sender, recipientAddress, nativeAmount);
    }

    function holdingsWithdrawToken(address recipientAddress, IERC20 tokenAddress, uint256 tokenAmount) public onlyOwner {
        require(recipientAddress != address(0), "PETS::withdraw: ZERO address.");

        uint256 totalbalance = tokenAddress.balanceOf(address(this));
        if( tokenAmount > totalbalance){tokenAmount = totalbalance;}
        tokenAddress.safeTransfer(recipientAddress, tokenAmount);
        emit WithdrawToken(address(tokenAddress), recipientAddress, tokenAmount);
    }

    function liquidityPoolCreate(address contractAddress, address routerAddress) internal onlyOwner returns (address){
        IUniswapV2Router02 router = IUniswapV2Router02(routerAddress);
        address lpPair = IUniswapV2Factory(router.factory()).createPair(address(this), contractAddress);
        liquidityPoolAddress = lpPair;
        return lpPair;
    }

    function liquidityPoolUpdate(address newLiquidityPoolAddress) public onlyOwner {
        liquidityPoolAddress = newLiquidityPoolAddress;
    }    

    function maxTransferLiquidityPool() public view returns (uint256) {
        return balanceOf(liquidityPoolAddress).mul(maxTransferAmountLiquidityPoolPercent).div(10000000000);
    }

    function maxTransferLiquidityPoolUpdate(uint256 newTransferAmountRate) public onlyOwner {
        emit MaxTransferAmountLiquidityPoolRateUpdated(msg.sender, maxTransferAmountLiquidityPoolPercent, newTransferAmountRate); 
        maxTransferAmountLiquidityPoolPercent = newTransferAmountRate;
    }       

    function startBlockUpdate(uint256 startAtBlock) public onlyOwner {
        startBlock = startAtBlock;
    }

    function timeLimitSwapUpdate(uint256 numberOfBlocks) public onlyOwner {
		require(numberOfBlocks <= 28800, "PETS::UpdateTimeLimitSwap: Too long.");
        emit TimeLimitSwapUpdated(msg.sender, numberOfBlocks);
        timeLimitSwap = numberOfBlocks;
    }

    function taxRateAdd(address recipientAddress, string memory recipientName, uint256 recipientTaxRate) onlyOwner public returns (bool){     
        taxRecipientName[recipientAddress] = recipientName;
        taxRecipientRate[recipientAddress] = recipientTaxRate;
        if(!isInTaxMap[recipientAddress]) {
            isInTaxMap[recipientAddress] = true;
            taxKeys.push(recipientAddress);
        }
        return true;
    }

    function taxRateCount() public view returns (uint256){
        return taxKeys.length;
    }

    function taxRateDelete(address recipientAddress) onlyOwner public returns (bool){
        if(isInTaxMap[recipientAddress]) {
            delete taxRecipientName[recipientAddress];
            delete taxRecipientRate[recipientAddress];
            delete isInTaxMap[recipientAddress];  
            return true;      
        }
        return false;
    }    

    function taxRateRecipientAmount(address recipientAddress) public view returns(uint256){
        if(isInTaxMap[recipientAddress]) {
            return taxRecipientRate[recipientAddress];
        }
        return 0;
    }

    function taxRateRecipientName(address recipientAddress) public view returns(string memory){
        if(isInTaxMap[recipientAddress]) {
            return taxRecipientName[recipientAddress];
        }
        return "Not Found";
    }    

    function taxRateTotal() public view returns (uint256){
        uint256 recipientTaxRate = 0;
        for(uint i; i < taxKeys.length; ++i){
            recipientTaxRate = recipientTaxRate + taxRecipientRate[taxKeys[i]];
        }
        return recipientTaxRate;
    }

    function mint(address to, uint256 amount) public onlyOwner {
        _mint(to, amount);
    }

    function pause() public onlyOwner {
        _pause();
    }

    function unpause() public onlyOwner {
        _unpause();
    }

    function snapshot() public onlyOwner {
        _snapshot();
    }

    function _authorizeUpgrade(address newImplementation)
        internal
        onlyOwner
        override
    {}

    function _beforeTokenTransfer(address from, address to, uint256 amount)
        internal
        whenNotPaused
        override(ERC20Upgradeable, ERC20SnapshotUpgradeable)
    {
        super._beforeTokenTransfer(from, to, amount);
    }

    function _transfer(address sender, address recipient, uint256 amount) 
        internal whenNotPaused virtual override 
        antiWhale(sender, recipient, amount) 
        {

        address userAddress = address(0);
        if (sender == liquidityPoolAddress){
            userAddress = recipient;
        }
        else {
            userAddress = sender;
        }

        require(!blacklisted[sender] && !blacklisted[recipient], 'Address address has been Blacklisted - Please Contact Support');
        require(block.number >= startBlock, 'Starting Block Not Met');
        
        if (userAddress != address(0)){
            if (lastUserSwap[userAddress] > 0) {
                uint256 lastSwap = lastUserSwap[userAddress];
                uint256 checkLastSwap = block.number.sub(lastSwap);
                require(checkLastSwap >= timeLimitSwap, 'Starting Block Not Met');	
            }																
            lastUserSwap[userAddress] = block.number;
        }

        if(!allowSelling && sender != owner() && sender != address(this) && !excludedFromLimitSwap[sender]){
            require(recipient != liquidityPoolAddress, "PETS: Selling disabled");
        }

        if(!allowBuying && recipient != owner() && !excludedFromLimitSwap[recipient]){
            require(sender != liquidityPoolAddress,"PETS: Buying disabled");
        }

        if((!excludedFromFees[sender] && !excludedFromFees[recipient]) ){
            uint256 finalAmount = amount;
            for(uint i; i < taxKeys.length; ++i){
                if(isInTaxMap[taxKeys[i]]) {
                    require(distributionHandlerAddress != address(0),"No Distribution Wallet Set");
                    uint256 taxAmount = amount.mul(taxRecipientRate[taxKeys[i]]).div(10000);
                    finalAmount = finalAmount.sub(taxAmount);
                    // Distribution distribution = Distribution(distributionHandlerAddress)
                    // distribution.deposit{value:taxAmount}(taxKeys[i]);
                    //distributionHandlerAddress.deposit.value(taxAmount)(taxKeys[i], recipient);
                    super._transfer(sender, taxKeys[i], taxAmount);
                }
            }

            //address.func.value(amount)(arg1, arg2, arg3)
            super._transfer(sender, recipient, finalAmount);
        }else{
            super._transfer(sender, recipient, amount);
        }
    }

}