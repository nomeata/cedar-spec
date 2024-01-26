permit(
  principal == a::"l",
  action in [Action::"action"],
  resource is a in a::"l"
) when {
  true && (if {"A": action, "CgliqjX2h0hghhhhi": !principal} then (!(!action)) else (!(!context)))
};
