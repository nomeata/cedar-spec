permit(
  principal in a::"",
  action in [Action::"action"],
  resource == a::"jl"
) when {
  true && ("".isLoopback())
};
