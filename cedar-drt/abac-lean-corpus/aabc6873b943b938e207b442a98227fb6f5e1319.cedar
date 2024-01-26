permit(
  principal == a::"l",
  action in [Action::"action"],
  resource is a in a::"l"
) when {
  true && (if {"CgliqjX2h0hghhhhi": !principal, "A": action} then (!(!action)) else (!(!action)))
};
