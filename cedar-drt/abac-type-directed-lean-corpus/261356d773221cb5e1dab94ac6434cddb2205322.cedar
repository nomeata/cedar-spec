permit(
  principal == a::"\'2333@14&\u{16}666",
  action in [Action::""],
  resource
) when {
  true && (a::"\'2333@14&\u{16}666" has "BcpD")
};
